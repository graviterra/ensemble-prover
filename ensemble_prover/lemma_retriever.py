"""Build and query versioned Lean-declaration retrieval indexes."""

from __future__ import annotations

import hashlib
import json
import logging
import math
import os
import random
import re
import tempfile
import threading
import time
from collections import Counter, OrderedDict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Tuple

from .artifact_versions import (
    LEMMA_INDEX_META_SCHEMA_VERSION,
    STATEMENT_PARSER_VERSION,
    current_lemma_index_versions,
    stamp_versions,
    versions_match,
)
from .config import LeanConfig, RetrievalConfig
from .domain import DomainHint
from .embeddings import EmbedderConfig, TextEmbedder, make_embedder
from .lean_decl_parser import find_decl_header_end
from .math_utils import cosine_sim as _cosine_sim
from .math_utils import sigmoid as _math_sigmoid
from .mini_prompt_support import STEERING_DIRECTIVE
from .putnam import is_putnam_bench_problem_source
from .theorem_project import scan_lean_declarations
from .tokenizer import TOKEN_RE as _TOKEN_RE
from .tokenizer import sanitize_for_json as _sanitize_for_json
from .tokenizer import (  # noqa: F401 — re-exported for backward compat
    tokenize as _tokenize,
)
from .utils import _first_top_level_colon_after, estimate_tokens

logger = logging.getLogger(__name__)
_HF_ENV_LOCK = threading.Lock()

try:  # optional dependency: enables fast dense retrieval over full index
    import numpy as np  # type: ignore
except Exception:  # pragma: no cover
    np = None  # type: ignore

_DENSE_WARNED = False
_DENSE_EMBED_WORKER_SLOTS = threading.BoundedSemaphore(2)
_ONLINE_EMBED_WORKER_SLOTS = threading.BoundedSemaphore(2)
_ONLINE_EMBED_BATCH_TIMEOUT_S = 12.0


_DECL_RE = re.compile(
    r"(?m)^\s*(?:@\[.*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(theorem|lemma|def|abbrev|instance)\s+([A-Za-z0-9_'.]+)\b"
)


def _online_embed_many_with_watchdog(
    embedder: Any,
    texts: List[str],
    *,
    timeout_s: Optional[float] = None,
) -> List[List[float]]:
    """Batch online candidate embeddings without holding retrieval forever."""

    if not texts:
        return []
    embed_many = getattr(embedder, "embed_many", None)
    if not _ONLINE_EMBED_WORKER_SLOTS.acquire(blocking=False):
        raise RuntimeError("online embedding worker capacity exhausted")
    done = threading.Event()
    box: Dict[str, Any] = {"vectors": None, "error": None}

    def worker() -> None:
        try:
            if callable(embed_many):
                box["vectors"] = embed_many(texts)
            else:
                embed = getattr(embedder, "embed", None)
                if not callable(embed):
                    raise TypeError("online embedder exposes neither embed_many nor embed")
                box["vectors"] = [embed(text) for text in texts]
        except BaseException as exc:
            box["error"] = exc
        finally:
            _ONLINE_EMBED_WORKER_SLOTS.release()
            done.set()

    try:
        thread = threading.Thread(
            target=worker,
            name="mini-online-embed-batch",
            daemon=True,
        )
        thread.start()
    except BaseException:
        _ONLINE_EMBED_WORKER_SLOTS.release()
        raise
    effective_timeout_s = max(
        0.01,
        min(
            float(_ONLINE_EMBED_BATCH_TIMEOUT_S or 12.0),
            (
                float(timeout_s)
                if timeout_s is not None
                else float(_ONLINE_EMBED_BATCH_TIMEOUT_S or 12.0)
            ),
        ),
    )
    if not done.wait(timeout=effective_timeout_s):
        raise TimeoutError(
            "online embedding batch exceeded watchdog "
            f"({effective_timeout_s:.3f}s)"
        )
    error = box.get("error")
    if error is not None:
        raise error
    return [list(vector or []) for vector in list(box.get("vectors") or ())]


_NAMESPACE_RE = re.compile(r"(?m)^\s*namespace\s+([A-Za-z0-9_'.]+)\b")
_SECTION_RE = re.compile(
    r"(?m)^\s*(?:@\[.*?\]\s*)?(?:public\s+|protected\s+)?section\b(?:\s+([A-Za-z0-9_'.]+))?"
)
_END_RE = re.compile(r"(?m)^\s*end\b(?:\s+([A-Za-z0-9_'.]+))?")
_DOCSTRING_RE = re.compile(r"/--(.*?)-/", re.DOTALL)
_LEAN_SYMBOL_RE = re.compile(r"[∀∃→↔=<>≤≥∈⊆∣∧∨¬⊢]|->|=>|:=|≠")


def _atomic_write_text(path: Path, content: str) -> None:
    """Write *content* to *path* atomically via temp-file + rename."""
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=str(path.parent), suffix=".tmp")
    try:
        with open(fd, "w", encoding="utf-8") as f:
            f.write(content)
        Path(tmp).replace(path)
    except BaseException:
        Path(tmp).unlink(missing_ok=True)
        raise


def _extract_symbols(text: str) -> List[str]:
    return list(dict.fromkeys(_LEAN_SYMBOL_RE.findall(text)))


def _estimate_tokens(text: str, *, model: Optional[str] = None) -> int:
    """Cheap token estimator for prompt budgeting (dependency-free)."""
    s = (text or "").strip()
    if not s:
        return 0
    return max(1, int(estimate_tokens(s, model=model)))


def _normalize_stmt(s: str) -> str:
    return re.sub(r"\s+", " ", (s or "").strip())


def _hf_hub_cache_roots() -> List[Path]:
    """Candidate Hugging Face hub roots in priority order."""
    roots: List[Path] = []
    env_hub = os.environ.get("HUGGINGFACE_HUB_CACHE")
    if env_hub:
        roots.append(Path(env_hub))
    env_hf_home = os.environ.get("HF_HOME")
    if env_hf_home:
        roots.append(Path(env_hf_home) / "hub")
    env_xdg = os.environ.get("XDG_CACHE_HOME")
    if env_xdg:
        roots.append(Path(env_xdg) / "huggingface" / "hub")
    roots.append(Path.home() / ".cache" / "huggingface" / "hub")

    out: List[Path] = []
    seen: set[str] = set()
    for root in roots:
        key = str(root)
        if key in seen:
            continue
        seen.add(key)
        if root.exists():
            out.append(root)
    return out


def _resolve_hf_snapshot_path(model_name: str) -> Optional[Path]:
    """Resolve a HF repo id (e.g. org/name) to a local cached snapshot path."""
    p = Path(model_name)
    if p.exists():
        return p
    if "/" not in model_name:
        return None

    repo_dir_name = f"models--{model_name.replace('/', '--')}"
    for hub_root in _hf_hub_cache_roots():
        repo_dir = hub_root / repo_dir_name
        if not repo_dir.exists():
            continue

        candidates: List[Path] = []
        refs_dir = repo_dir / "refs"
        if refs_dir.exists():
            for ref_file in refs_dir.iterdir():
                if not ref_file.is_file():
                    continue
                try:
                    snap = ref_file.read_text(encoding="utf-8").strip()
                except Exception:
                    continue
                if snap:
                    candidates.append(repo_dir / "snapshots" / snap)

        snaps_dir = repo_dir / "snapshots"
        if snaps_dir.exists():
            # Add newest snapshots as fallback if refs are stale/missing.
            try:
                newest = sorted(
                    [d for d in snaps_dir.iterdir() if d.is_dir()],
                    key=lambda d: d.stat().st_mtime,
                    reverse=True,
                )
                candidates.extend(newest)
            except Exception:
                pass

        seen: set[str] = set()
        for cand in candidates:
            ckey = str(cand)
            if ckey in seen:
                continue
            seen.add(ckey)
            if not cand.exists():
                continue
            # Basic integrity check so we don't return empty snapshot dirs.
            if (cand / "config.json").exists() or (cand / "tokenizer.json").exists():
                return cand
    return None


def _jaccard(a: str, b: str) -> float:
    at = set(_TOKEN_RE.findall((a or "").lower()))
    bt = set(_TOKEN_RE.findall((b or "").lower()))
    if not at or not bt:
        return 0.0
    return len(at & bt) / max(1, len(at | bt))


@dataclass
class LemmaEntry:
    name: str
    type: str
    file: str
    kind: str = "theorem"
    namespace: str = ""
    docstring: str = ""
    source: str = "mathlib"


@dataclass
class LemmaIndexMeta:
    created_ts: float
    fingerprint: str
    file_count: int
    lemma_count: int
    config_fingerprint: str = ""
    source_counts: Dict[str, int] = field(default_factory=dict)
    artifact_schema_version: int = LEMMA_INDEX_META_SCHEMA_VERSION
    statement_parser_version: str = STATEMENT_PARSER_VERSION


class LemmaIndex:
    def __init__(self, entries: Optional[List[LemmaEntry]] = None):
        self.entries: List[LemmaEntry] = entries or []
        self.inv_index: Dict[str, List[Tuple[int, int]]] = {}
        self.doc_len: List[int] = []
        self.name_tokens: List[List[str]] = []
        self.symbols: List[List[str]] = []
        self.avg_len: float = 0.0
        self.df: Dict[str, int] = {}
        self.idf: Dict[str, float] = {}

    def prepare(self) -> None:
        self.inv_index = {}
        self.doc_len = []
        self.name_tokens = []
        self.symbols = []
        self.df = {}
        for idx, entry in enumerate(self.entries):
            text = f"{entry.name} {entry.type} {entry.docstring}"
            tokens = _tokenize(text)
            self.doc_len.append(len(tokens))
            self.name_tokens.append(_tokenize(entry.name))
            self.symbols.append(_extract_symbols(entry.type))
            tf: Dict[str, int] = {}
            for t in tokens:
                tf[t] = tf.get(t, 0) + 1
            for t, cnt in tf.items():
                self.inv_index.setdefault(t, []).append((idx, cnt))
                self.df[t] = self.df.get(t, 0) + 1
        n = max(1, len(self.entries))
        self.avg_len = sum(self.doc_len) / max(1, len(self.doc_len))
        self.idf = {}
        for tok, df in self.df.items():
            self.idf[tok] = math.log((n - df + 0.5) / (df + 0.5) + 1.0)

    def save(self, path: Path, meta_path: Path, meta: LemmaIndexMeta) -> None:
        index_content = "".join(
            json.dumps(e.__dict__, ensure_ascii=False) + "\n" for e in self.entries
        )
        _atomic_write_text(path, index_content)
        _atomic_write_text(meta_path, json.dumps(meta.__dict__))

    @staticmethod
    def load(path: Path) -> Optional["LemmaIndex"]:
        if not path.exists():
            return None
        entries: List[LemmaEntry] = []
        for line in path.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            try:
                data = json.loads(line)
                entries.append(LemmaEntry(**data))
            except Exception as exc:
                logger.debug(
                    "LemmaIndex.load: skipping corrupted entry in %s: %s", path, exc
                )
                continue
        idx = LemmaIndex(entries)
        idx.prepare()
        return idx


def _fingerprint_files(paths: Iterable[Path]) -> str:
    h = hashlib.sha256()
    count = 0
    # L8 fix: sort by path string so fingerprint is filesystem-order-independent.
    for p in sorted(paths, key=lambda x: str(x)):
        try:
            st = p.stat()
        except FileNotFoundError:
            continue
        rel = str(p)
        h.update(rel.encode("utf-8"))
        h.update(str(st.st_mtime_ns).encode("utf-8"))
        h.update(str(st.st_size).encode("utf-8"))
        try:
            with p.open("rb") as fh:
                while True:
                    chunk = fh.read(1024 * 1024)
                    if not chunk:
                        break
                    h.update(chunk)
        except Exception as exc:
            logger.debug(
                "_fingerprint_files: failed to hash contents for %s: %s", p, exc
            )
            h.update(b"<unreadable>")
        count += 1
    h.update(str(count).encode("utf-8"))
    return h.hexdigest()


def _config_fingerprint(cfg: RetrievalConfig) -> str:
    # Include config fields that affect project/support index contents.
    payload = stamp_versions(
        {
            "support_index_kind": "project_only",
            "include_docstrings": cfg.include_docstrings,
            "max_lemmas": cfg.max_lemmas,
            "include_project": cfg.include_project,
            "project_root": cfg.project_root or "",
            "bm25_k1": cfg.bm25_k1,
            "bm25_b": cfg.bm25_b,
        },
        current_lemma_index_versions(),
    )
    h = hashlib.sha256()
    h.update(json.dumps(payload, sort_keys=True).encode("utf-8"))
    return h.hexdigest()


def _entry_source_counts(entries: Sequence[LemmaEntry]) -> Dict[str, int]:
    counts = Counter(
        str(getattr(entry, "source", "") or "unknown") for entry in entries
    )
    return {key: int(value) for key, value in sorted(counts.items()) if int(value) > 0}


def _meta_source_counts(meta: Optional[Dict[str, Any]]) -> Dict[str, int]:
    if not isinstance(meta, dict):
        return {}
    raw = meta.get("source_counts")
    if not isinstance(raw, dict):
        return {}
    out: Dict[str, int] = {}
    for key, value in raw.items():
        try:
            count = int(value)
        except Exception:
            continue
        if count > 0:
            out[str(key)] = count
    return out


@dataclass
class ResolvedLemmaRoots:
    roots: List[Path]
    project_root: Optional[Path]
    missing_required: List[str]


def _resolve_project_dir_root(project_dir: str) -> Optional[Path]:
    project_path = Path(project_dir)
    resolved = project_path.resolve()
    if resolved.exists():
        return resolved
    pkg_root = Path(__file__).resolve().parent.parent
    resolved_fb = (pkg_root / project_path).resolve()
    if resolved_fb.exists():
        logger.info(
            "Project root found via package-root fallback: %s (cwd-relative %s did not exist)",
            resolved_fb,
            resolved,
        )
        return resolved_fb
    return None


def _resolve_retrieval_roots(
    cfg: RetrievalConfig, lean_cfg: LeanConfig
) -> ResolvedLemmaRoots:
    project_root: Optional[Path]
    if cfg.project_root:
        candidate = Path(str(cfg.project_root)).expanduser().resolve()
        project_root = candidate if candidate.exists() else None
    else:
        project_root = _resolve_project_dir_root(lean_cfg.project_dir)

    roots: List[Path] = []
    missing_required: List[str] = []
    if cfg.include_project:
        if project_root is not None:
            roots.append(project_root)
        else:
            missing_required.append("project")
    return ResolvedLemmaRoots(
        roots=roots,
        project_root=project_root,
        missing_required=missing_required,
    )


def _project_only_index(index: LemmaIndex) -> LemmaIndex:
    """Drop Mathlib entries from a mixed support index before runtime use."""
    entries = list(getattr(index, "entries", []) or [])
    kept = [
        entry
        for entry in entries
        if str(getattr(entry, "source", "") or "").strip().lower() != "mathlib"
    ]
    if len(kept) == len(entries):
        return index
    filtered = LemmaIndex(list(kept))
    filtered.prepare()
    return filtered


def _iter_lean_files(
    root: Path,
    *,
    exclude_dirs: Optional[Sequence[str]] = None,
    skip_putnam_bench_problem_sources: bool = False,
) -> Iterable[Path]:
    exclude = set(exclude_dirs or [])
    for path in sorted(
        root.rglob("*.lean"),
        key=lambda item: str(item.relative_to(root)),
    ):
        try:
            rel = path.relative_to(root)
            parts = rel.parts
        except Exception:
            parts = path.parts
        if any(part in exclude for part in parts):
            continue
        if skip_putnam_bench_problem_sources and is_putnam_bench_problem_source(path):
            continue
        yield path


def _extract_docstring_before(text: str, start_idx: int) -> str:
    prefix = text[:start_idx]
    end = prefix.rfind("-/")
    if end == -1:
        return ""
    start = prefix.rfind("/--", 0, end)
    if start == -1:
        return ""
    between = prefix[end + 2 :]
    if between.strip():
        return ""
    doc = prefix[start : end + 2]
    m = _DOCSTRING_RE.search(doc)
    if not m:
        return ""
    return m.group(1).strip()


def _extract_header(text: str, start_idx: int, max_scan: int = 4000) -> Optional[str]:
    end = find_decl_header_end(
        text,
        start_idx,
        max_scan=max_scan,
        allow_where=True,
    )
    if end is None:
        return None
    return text[start_idx:end]


def _header_to_type(header: str) -> tuple[str, str, str]:
    if ":=" in header:
        header = header.rsplit(":=", 1)[0]
    m = re.search(
        r"\b(theorem|lemma|def|abbrev|instance)\s+([A-Za-z0-9_'.]+)\b", header
    )
    if not m:
        raise ValueError("Header missing declaration name")
    kind = m.group(1)
    name = m.group(2)
    name_end = m.end()
    colon_pos = _first_top_level_colon_after(header, name_end)
    if colon_pos == -1:
        raise ValueError(f"Header for {name} missing top-level ':'")
    binder_part = header[name_end:colon_pos].strip()
    type_part = header[colon_pos + 1 :].strip()
    if binder_part:
        return name, f"∀ {binder_part}, {type_part}", kind
    return name, type_part, kind


def _scan_file(text: str, file_path: Path) -> List[LemmaEntry]:
    entries: List[LemmaEntry] = []
    try:
        declarations = scan_lean_declarations(text)
    except ValueError as exc:
        logger.debug("_scan_file: failed to scan %s: %s", file_path, exc)
        return entries
    for declaration in declarations:
        namespace = ".".join(declaration.namespace)
        entries.append(
            LemmaEntry(
                name=declaration.canonical_name,
                type=declaration.statement_type.strip(),
                file=str(file_path),
                kind=declaration.kind,
                namespace=namespace,
                docstring=declaration.docstring,
            )
        )
    return entries


def build_index(
    roots: Sequence[Path],
    *,
    max_lemmas: int = 250000,
    include_docstrings: bool = False,
    file_paths: Optional[Sequence[Path]] = None,
) -> LemmaIndex:
    entries: List[LemmaEntry] = []
    if file_paths is not None:
        all_paths: Iterable[Path] = file_paths
    else:
        all_paths = (
            p
            for root in roots
            if root and root.exists()
            for p in _iter_lean_files(
                root,
                exclude_dirs=["build", ".lake", ".git", "external", "Temp"],
                skip_putnam_bench_problem_sources=True,
            )
        )
    for path in all_paths:
        try:
            text = path.read_text(encoding="utf-8")
        except Exception as exc:
            logger.warning("build_index: failed to read %s: %s", path, exc)
            continue
        for e in _scan_file(text, path):
            if not include_docstrings:
                e.docstring = ""
            e.source = "mathlib" if "Mathlib" in path.parts else "project"
            entries.append(e)
            if len(entries) >= max_lemmas:
                break
        if len(entries) >= max_lemmas:
            break
    idx = LemmaIndex(entries)
    idx.prepare()
    return idx


class LemmaRetriever:
    """Dynamic project/support retriever for non-API grounding and reranking.

    This is no longer the authoritative library API search layer. Static
    Mathlib lookup lives in ``MathlibApiSearcher``; this class remains the
    dynamic support channel for project-indexed declarations, prompt-local
    declarations, and legacy reranking helpers.
    """

    def __init__(self, cfg: RetrievalConfig, lean_cfg: LeanConfig):
        self.cfg = cfg
        self.lean_cfg = lean_cfg
        self.index: Optional[LemmaIndex] = None
        self._embedding_cache: "OrderedDict[int, List[float]]" = OrderedDict()
        self._embedding_cache_size = max(0, int(cfg.embedding_cache_size))
        # Cache query embeddings (goal-conditioned queries can repeat across tactic loops).
        self._query_embedding_cache: "OrderedDict[str, List[float]]" = OrderedDict()
        self._query_embedding_cache_size = max(0, int(cfg.query_embedding_cache_size))
        self._embedder: Optional[TextEmbedder] = None
        self._embedder_init_error: str = ""
        self._tokenizer_model: Optional[str] = None
        # Dense semantic retrieval over the full index (optional)
        self._dense_matrix: Any = None  # numpy.ndarray (N, D) or list-of-lists fallback
        self._dense_ready: bool = False
        # Optional cross-encoder reranker (supports LLM-based or standard CrossEncoder)
        self._cross_encoder = None
        self._cross_encoder_is_llm: bool = False
        self._cross_encoder_cutoff_layers: List[int] = [28]
        self._cross_encoder_cache: "OrderedDict[str, float]" = OrderedDict()
        self._cross_encoder_cache_size = max(0, int(cfg.cross_encoder_cache_size))
        # Runtime safety: if layerwise scoring hangs/errors, disable it for this
        # process and route reranking through fallback CrossEncoder instead.
        self._cross_encoder_layerwise_disabled: bool = False
        self._cross_encoder_layerwise_disable_reason: str = ""
        self._cross_encoder_force_cpu_fallback: bool = False
        self._cross_encoder_disabled: bool = False
        self._cross_encoder_disable_kind: str = ""
        self._cross_encoder_disable_reason: str = ""
        self._cross_encoder_disabled_until_ts: float = 0.0
        self._cross_encoder_transient_failures: int = 0
        self._cross_encoder_last_failure_ts: float = 0.0
        # Optional learning-to-rank (LTR) state
        self._ltr_enabled = bool(cfg.ltr_enabled)
        self._ltr_weights: Dict[str, float] = {}
        self._ltr_bias: float = 0.0
        self._ltr_updates: int = 0
        self._ltr_feature_names: List[str] = [
            "bm25_norm",
            "symbol",
            "name",
            "dense",
            "rank",
            "rerank",
        ]
        self._last_rerank_scores: Dict[str, float] = {}
        self._ready = False
        self._load_or_build()
        global _DENSE_WARNED
        if self.cfg.dense_retrieval_enabled and np is None and not _DENSE_WARNED:
            logger.warning(
                "Dense retrieval requested but numpy is unavailable; falling back to sparse-only retrieval."
            )
            _DENSE_WARNED = True
        if self._ltr_enabled:
            self._ltr_load()
        try:
            logger.info("Support lemma retriever status: %s", self.get_status())
        except Exception as exc:
            logger.debug("LemmaRetriever: status report failed: %s", exc)

    def set_tokenizer_model(self, model: Optional[str]) -> None:
        """Provide a model hint for prompt token budgeting heuristics."""
        if model and str(model).strip():
            self._tokenizer_model = str(model).strip()
        else:
            self._tokenizer_model = None

    def get_status(self) -> Dict[str, Any]:
        """Return a compact status dict for observability/telemetry."""
        dense_enabled = bool(self.cfg.dense_retrieval_enabled)
        use_embeddings = bool(self.cfg.use_embeddings and self._embedder is not None)
        rerank_mode = str(self.cfg.rerank_mode or "none")
        now_ts = time.time()
        cooldown_remaining_s = 0.0
        if (
            self._cross_encoder_disable_kind == "transient"
            and self._cross_encoder_disabled_until_ts > now_ts
        ):
            cooldown_remaining_s = float(self._cross_encoder_disabled_until_ts - now_ts)
        return {
            "channel": "support_lemma_retriever",
            "ready": bool(self._ready),
            "index_loaded": bool(self.index is not None),
            "use_embeddings": use_embeddings,
            "embedding_backend": str(self.cfg.embedding_backend),
            "embedding_model": str(self.cfg.embedding_model),
            "embedding_dim": (
                int(getattr(self._embedder, "dim", 0))
                if self._embedder is not None
                else 0
            ),
            "embedding_init_error": str(self._embedder_init_error or ""),
            "dense_enabled": dense_enabled,
            "dense_ready": bool(self._dense_ready),
            "dense_search_mode": str(self.cfg.dense_search_mode),
            "dense_matrix_kind": (
                "numpy"
                if (np is not None and isinstance(self._dense_matrix, np.ndarray))
                else ("python" if self._dense_matrix is not None else "none")
            ),
            "rerank_mode": rerank_mode,
            "cross_encoder_loaded": bool(self._cross_encoder is not None),
            "cross_encoder_force_sentence_transformers": bool(
                getattr(self.cfg, "cross_encoder_force_sentence_transformers", False)
            ),
            "cross_encoder_layerwise_disabled": bool(
                self._cross_encoder_layerwise_disabled
            ),
            "cross_encoder_layerwise_disable_reason": str(
                self._cross_encoder_layerwise_disable_reason or ""
            ),
            "cross_encoder_force_cpu_fallback": bool(
                self._cross_encoder_force_cpu_fallback
            ),
            "cross_encoder_disabled": bool(self._cross_encoder_disabled),
            "cross_encoder_disable_kind": str(self._cross_encoder_disable_kind or ""),
            "cross_encoder_disable_reason": str(
                self._cross_encoder_disable_reason or ""
            ),
            "cross_encoder_cooldown_remaining_s": float(cooldown_remaining_s),
            "cross_encoder_transient_failures": int(
                self._cross_encoder_transient_failures
            ),
            "cross_encoder_last_failure_ts": float(
                self._cross_encoder_last_failure_ts or 0.0
            ),
            "ltr_enabled": bool(self._ltr_enabled),
            "ltr_updates": int(self._ltr_updates),
            "query_embedding_cache": {
                "size": len(self._query_embedding_cache),
                "max": int(self._query_embedding_cache_size),
            },
            "lemma_embedding_cache": {
                "size": len(self._embedding_cache),
                "max": int(self._embedding_cache_size),
            },
            "cross_encoder_cache": {
                "size": len(self._cross_encoder_cache),
                "max": int(self._cross_encoder_cache_size),
            },
        }

    def supports_project_retrieval(self) -> bool:
        """True when the project/support retrieval index is active."""
        return bool(self._ready and self.index is not None)

    def _disable_layerwise_reranker(self, reason: str) -> None:
        msg = str(reason or "unknown")
        self._cross_encoder_layerwise_disabled = True
        self._cross_encoder_layerwise_disable_reason = msg
        self._cross_encoder_force_cpu_fallback = True
        self._cross_encoder = None
        self._cross_encoder_is_llm = False

    def _clear_cross_encoder_disable(self) -> None:
        self._cross_encoder_disabled = False
        self._cross_encoder_disable_kind = ""
        self._cross_encoder_disable_reason = ""
        self._cross_encoder_disabled_until_ts = 0.0

    def _mark_cross_encoder_success(self) -> None:
        self._cross_encoder_transient_failures = 0
        if (
            self._cross_encoder_disable_kind == "transient"
            or self._cross_encoder_disabled
        ):
            self._clear_cross_encoder_disable()

    def _cross_encoder_is_temporarily_disabled(self) -> bool:
        if not self._cross_encoder_disabled:
            return False
        if self._cross_encoder_disable_kind != "transient":
            return True
        now_ts = time.time()
        if now_ts < self._cross_encoder_disabled_until_ts:
            return True
        self._clear_cross_encoder_disable()
        logger.info("Cross-encoder transient cooldown elapsed; retrying load.")
        return False

    def _classify_cross_encoder_failure(self, exc: BaseException, *, stage: str) -> str:
        """Classify a cross-encoder failure as transient or permanent."""
        exc_name = exc.__class__.__name__.lower()
        msg = str(exc or "").lower()

        # Local-only runs should not be retried indefinitely when cache misses or
        # HF hub probes leak through as DNS errors.
        if "downloads disabled" in msg or "local-only load failed" in msg:
            return "permanent"

        transient_type_hints = (
            "timeout",
            "connectionerror",
            "connecttimeout",
            "readtimeout",
            "maxretryerror",
            "nameresolutionerror",
            "httpx",
        )
        if any(tok in exc_name for tok in transient_type_hints):
            return "transient"
        if isinstance(exc, TimeoutError):
            return "transient"

        permanent_msg_hints = (
            "downloads disabled",
            "local-only load failed",
            "no module named",
            "cannot import name",
            "is_torch_fx_available",
            "repository not found",
            "not a valid model identifier",
            "401 client error",
            "403 client error",
            "404 client error",
            "invalid device",
            "unsupported device",
            "unrecognized configuration class",
            "trust_remote_code",
        )
        if any(tok in msg for tok in permanent_msg_hints):
            return "permanent"

        transient_msg_hints = (
            "temporary failure in name resolution",
            "failed to resolve",
            "max retries exceeded",
            "connection reset",
            "connection refused",
            "network is unreachable",
            "timed out",
            "service unavailable",
            "too many requests",
            "rate limit",
            "resource temporarily unavailable",
            "read timeout",
            "connect timeout",
            "cuda out of memory",
            "cudnn",
            "cublas",
            "device-side assert",
            "driver shutting down",
        )
        if any(tok in msg for tok in transient_msg_hints):
            return "transient"

        if isinstance(exc, (ModuleNotFoundError, ImportError)):
            return "permanent"
        if isinstance(exc, (ValueError, TypeError, RuntimeError)):
            if (
                stage in ("load", "predict")
                and "not found in local cache" in msg
                and "internet access" in msg
            ):
                return "permanent"
            # RuntimeError is broad; treat as transient by default and escalate
            # after repeated failures.
            return "transient"
        return "transient"

    def _disable_cross_encoder(self, reason: str, *, kind: str = "permanent") -> None:
        msg = str(reason or "unknown")
        self._cross_encoder = None
        self._cross_encoder_is_llm = False
        self._cross_encoder_last_failure_ts = time.time()
        if kind == "transient":
            self._cross_encoder_transient_failures += 1
            max_failures = max(
                1, int(getattr(self.cfg, "cross_encoder_max_transient_failures", 3))
            )
            if self._cross_encoder_transient_failures >= max_failures:
                self._cross_encoder_disabled = True
                self._cross_encoder_disable_kind = "permanent"
                self._cross_encoder_disable_reason = f"escalated_after_transient_failures({self._cross_encoder_transient_failures}/{max_failures}): {msg}"
                self._cross_encoder_disabled_until_ts = 0.0
                logger.warning(
                    "Cross-encoder transient failures reached limit (%d/%d); disabling permanently for this process.",
                    self._cross_encoder_transient_failures,
                    max_failures,
                )
                return
            cooldown_s = max(
                1.0,
                float(getattr(self.cfg, "cross_encoder_transient_cooldown_s", 120.0)),
            )
            self._cross_encoder_disabled = True
            self._cross_encoder_disable_kind = "transient"
            self._cross_encoder_disable_reason = msg
            self._cross_encoder_disabled_until_ts = (
                self._cross_encoder_last_failure_ts + cooldown_s
            )
            logger.warning(
                "Cross-encoder transient failure; disabling for %.1fs (%d/%d): %s",
                cooldown_s,
                self._cross_encoder_transient_failures,
                max_failures,
                msg,
            )
            return

        self._cross_encoder_disabled = True
        self._cross_encoder_disable_kind = "permanent"
        self._cross_encoder_disable_reason = msg
        self._cross_encoder_disabled_until_ts = 0.0

    def on_problem_start(self) -> None:
        """Problem-boundary hook for resetting transient reranker suppressions."""
        if not bool(getattr(self.cfg, "cross_encoder_reset_on_problem_start", True)):
            return
        if self._cross_encoder_disable_kind == "transient":
            logger.info(
                "Resetting transient cross-encoder disable at problem start: %s",
                self._cross_encoder_disable_reason or "unknown",
            )
            self._clear_cross_encoder_disable()
        elif (
            self._cross_encoder_disable_kind == "permanent"
            and "escalated_after_transient_failures"
            in (self._cross_encoder_disable_reason or "")
        ):
            # Escalated-from-transient disables get a fresh chance each problem.
            # True permanent errors (module not found, import failed) stay disabled.
            logger.info(
                "Resetting escalated cross-encoder disable at problem start: %s",
                self._cross_encoder_disable_reason or "unknown",
            )
            self._cross_encoder_transient_failures = 0
            self._clear_cross_encoder_disable()

    def _compute_layerwise_scores_with_timeout(
        self,
        pairs: List[List[str]],
    ) -> Tuple[Optional[Any], Optional[BaseException]]:
        """Run layerwise compute_score with a hard timeout.

        The layerwise model occasionally stalls inside generation/scoring; this
        guard avoids blocking the prover pipeline indefinitely.
        """
        timeout_s = max(
            1.0, float(getattr(self.cfg, "cross_encoder_score_timeout_s", 20.0))
        )
        done = threading.Event()
        box: Dict[str, Any] = {"preds": None, "exc": None}

        def _worker() -> None:
            try:
                if self._cross_encoder is None:
                    raise RuntimeError("cross_encoder is None")
                box["preds"] = self._cross_encoder.compute_score(
                    pairs,
                    cutoff_layers=self._cross_encoder_cutoff_layers,
                    normalize=True,
                )
            except BaseException as exc:
                box["exc"] = exc
            finally:
                done.set()

        t = threading.Thread(
            target=_worker,
            name="layerwise-rerank-worker",
            daemon=True,
        )
        t.start()
        if not done.wait(timeout=timeout_s):
            return None, TimeoutError(
                f"layerwise compute_score exceeded timeout ({timeout_s:.1f}s)"
            )
        return box.get("preds"), box.get("exc")

    def _predict_cross_encoder_with_timeout(
        self,
        pairs: List[Tuple[str, str]],
    ) -> Tuple[Optional[Any], Optional[BaseException]]:
        """Run standard CrossEncoder.predict with a hard timeout."""
        timeout_s = max(
            1.0, float(getattr(self.cfg, "cross_encoder_score_timeout_s", 20.0))
        )
        done = threading.Event()
        box: Dict[str, Any] = {"preds": None, "exc": None}

        def _worker() -> None:
            try:
                if self._cross_encoder is None:
                    raise RuntimeError("cross_encoder is None")
                box["preds"] = self._cross_encoder.predict(pairs)
            except BaseException as exc:
                box["exc"] = exc
            finally:
                done.set()

        t = threading.Thread(
            target=_worker,
            name="cross-encoder-rerank-worker",
            daemon=True,
        )
        t.start()
        if not done.wait(timeout=timeout_s):
            return None, TimeoutError(
                f"cross-encoder predict exceeded timeout ({timeout_s:.1f}s)"
            )
        return box.get("preds"), box.get("exc")

    def _load_layerwise_reranker_with_timeout(
        self,
        model_name: str,
        *,
        use_fp16: bool,
        device: Optional[str],
    ) -> Tuple[Optional[Any], Optional[BaseException]]:
        timeout_s = max(
            1.0, float(getattr(self.cfg, "cross_encoder_score_timeout_s", 20.0))
        )
        prefer_local = bool(getattr(self.cfg, "embedding_prefer_local_files", True))
        local_only = bool(getattr(self.cfg, "embedding_local_files_only", False))
        allow_download = bool(getattr(self.cfg, "embedding_allow_download", True))
        resolved_model = _resolve_hf_snapshot_path(model_name)
        model_target = str(resolved_model) if resolved_model is not None else model_name
        is_local_path = Path(model_target).exists()
        done = threading.Event()
        box: Dict[str, Any] = {"model": None, "exc": None}
        want_offline = bool(
            prefer_local or local_only or is_local_path or not allow_download
        )

        def _worker() -> None:
            try:
                from FlagEmbedding import LayerWiseFlagLLMReranker  # type: ignore

                box["model"] = LayerWiseFlagLLMReranker(
                    model_target,
                    use_fp16=use_fp16,
                    device=device,
                )
            except BaseException as exc:
                box["exc"] = exc
            finally:
                done.set()

        # Lock + env-var mutation owned by main thread so timeout
        # always releases the lock (prevents permanent deadlock).
        prev_hf: Optional[str] = None
        prev_tx: Optional[str] = None
        if want_offline:
            _HF_ENV_LOCK.acquire()
            prev_hf = os.environ.get("HF_HUB_OFFLINE")
            prev_tx = os.environ.get("TRANSFORMERS_OFFLINE")
            os.environ["HF_HUB_OFFLINE"] = "1"
            os.environ["TRANSFORMERS_OFFLINE"] = "1"
        try:
            t = threading.Thread(
                target=_worker,
                name="layerwise-reranker-load-worker",
                daemon=True,
            )
            t.start()
            if not done.wait(timeout=timeout_s):
                return None, TimeoutError(
                    f"layerwise reranker load exceeded timeout ({timeout_s:.1f}s)"
                )
            return box.get("model"), box.get("exc")
        finally:
            if want_offline:
                if prev_hf is None:
                    os.environ.pop("HF_HUB_OFFLINE", None)
                else:
                    os.environ["HF_HUB_OFFLINE"] = prev_hf
                if prev_tx is None:
                    os.environ.pop("TRANSFORMERS_OFFLINE", None)
                else:
                    os.environ["TRANSFORMERS_OFFLINE"] = prev_tx
                _HF_ENV_LOCK.release()

    def _load_cross_encoder_with_timeout(
        self,
        model_name: str,
        *,
        device: Optional[str],
    ) -> Tuple[Optional[Any], Optional[BaseException]]:
        timeout_s = max(
            1.0, float(getattr(self.cfg, "cross_encoder_score_timeout_s", 20.0))
        )
        prefer_local_files = bool(
            getattr(self.cfg, "embedding_prefer_local_files", True)
        )
        local_files_only = bool(getattr(self.cfg, "embedding_local_files_only", False))
        allow_download = bool(getattr(self.cfg, "embedding_allow_download", True))
        resolved_model = _resolve_hf_snapshot_path(model_name)
        model_target = str(resolved_model) if resolved_model is not None else model_name
        is_local_path = Path(model_target).exists()
        want_local_first = bool(
            local_files_only
            or prefer_local_files
            or is_local_path
            or not allow_download
        )

        def _load(local_only: bool) -> Any:
            from sentence_transformers import CrossEncoder  # type: ignore

            kwargs: Dict[str, Any] = {}
            if device is not None:
                kwargs["device"] = device
            kwargs["local_files_only"] = bool(local_only)
            try:
                return CrossEncoder(model_target, **kwargs)
            except TypeError:
                # Back-compat for older ST versions without local_files_only kwarg.
                kwargs.pop("local_files_only", None)
                return CrossEncoder(model_target, **kwargs)

        def _run_load(
            local_only: bool, *, label: str
        ) -> Tuple[Optional[Any], Optional[BaseException]]:
            done = threading.Event()
            box: Dict[str, Any] = {"model": None, "exc": None}

            def _worker() -> None:
                try:
                    box["model"] = _load(local_only)
                except BaseException as exc:
                    box["exc"] = exc
                finally:
                    done.set()

            # Lock + env-var mutation owned by main thread so timeout
            # always releases the lock (prevents permanent deadlock).
            prev_hf: Optional[str] = None
            prev_tx: Optional[str] = None
            if local_only:
                _HF_ENV_LOCK.acquire()
                prev_hf = os.environ.get("HF_HUB_OFFLINE")
                prev_tx = os.environ.get("TRANSFORMERS_OFFLINE")
                os.environ["HF_HUB_OFFLINE"] = "1"
                os.environ["TRANSFORMERS_OFFLINE"] = "1"
            try:
                t = threading.Thread(target=_worker, name=label, daemon=True)
                t.start()
                if not done.wait(timeout=timeout_s):
                    mode = "local" if local_only else "network"
                    return None, TimeoutError(
                        f"cross-encoder {mode} load exceeded timeout ({timeout_s:.1f}s)"
                    )
                return box.get("model"), box.get("exc")
            finally:
                if local_only:
                    if prev_hf is None:
                        os.environ.pop("HF_HUB_OFFLINE", None)
                    else:
                        os.environ["HF_HUB_OFFLINE"] = prev_hf
                    if prev_tx is None:
                        os.environ.pop("TRANSFORMERS_OFFLINE", None)
                    else:
                        os.environ["TRANSFORMERS_OFFLINE"] = prev_tx
                    _HF_ENV_LOCK.release()

        local_exc: Optional[BaseException] = None
        if want_local_first:
            model, local_exc = _run_load(
                True,
                label="cross-encoder-local-load-worker",
            )
            if local_exc is None and model is not None:
                return model, None
            if local_files_only or is_local_path or not allow_download:
                return None, RuntimeError(
                    f"cross-encoder local-only load failed for '{model_name}' "
                    f"(downloads disabled): {local_exc}"
                )

        model, net_exc = _run_load(False, label="cross-encoder-load-worker")
        if net_exc is None and model is not None:
            return model, None
        if local_exc is not None and net_exc is not None:
            return None, RuntimeError(
                f"cross-encoder load failed: local={local_exc}; network={net_exc}"
            )
        return model, net_exc

    def _auto_mathlib_root(self) -> Optional[Path]:
        project_dir = Path(self.lean_cfg.project_dir)
        # Try resolving relative to cwd first (backwards compat)
        resolved = project_dir.resolve()
        candidate = resolved / ".lake" / "packages" / "mathlib" / "Mathlib"
        if candidate.exists():
            return candidate
        # Fallback: resolve relative to package root (parent of ensemble_prover/)
        pkg_root = Path(__file__).resolve().parent.parent
        resolved_fb = (pkg_root / project_dir).resolve()
        candidate_fb = resolved_fb / ".lake" / "packages" / "mathlib" / "Mathlib"
        if candidate_fb.exists():
            logger.info(
                "Mathlib found via package-root fallback: %s (cwd-relative %s did not exist)",
                candidate_fb,
                candidate,
            )
            return candidate_fb
        return None

    def _auto_project_root(self) -> Optional[Path]:
        project_dir = Path(self.lean_cfg.project_dir)
        resolved = project_dir.resolve()
        if resolved.exists():
            return resolved
        # Fallback: resolve relative to package root
        pkg_root = Path(__file__).resolve().parent.parent
        resolved_fb = (pkg_root / project_dir).resolve()
        if resolved_fb.exists():
            logger.info(
                "Project root found via package-root fallback: %s (cwd-relative %s did not exist)",
                resolved_fb,
                resolved,
            )
            return resolved_fb
        return None

    def _load_or_build(self) -> None:
        if not bool(self.cfg.include_project):
            logger.info(
                "LemmaRetriever: project/support retrieval disabled (include_project=false)."
            )
            self.index = None
            self._ready = False
            return

        index_path = Path(self.cfg.index_path)
        meta_path = Path(self.cfg.meta_path)
        meta = None
        active_meta: Optional[Dict[str, Any]] = None
        if meta_path.exists():
            try:
                meta = json.loads(meta_path.read_text(encoding="utf-8"))
            except Exception as exc:
                logger.warning(
                    "_load_or_build: failed to parse meta %s: %s", meta_path, exc
                )
                meta = None
        if isinstance(meta, dict):
            active_meta = meta

        resolved_roots = _resolve_retrieval_roots(self.cfg, self.lean_cfg)
        roots = resolved_roots.roots

        exclude_dirs_list = ["build", ".lake", ".git", "external", "Temp"]
        all_files = [
            p
            for r in roots
            for p in _iter_lean_files(
                r,
                exclude_dirs=exclude_dirs_list,
                skip_putnam_bench_problem_sources=True,
            )
        ]
        fingerprint = _fingerprint_files(all_files)
        cfg_fp = _config_fingerprint(self.cfg)
        expected_versions = current_lemma_index_versions()
        existing_index: Optional[LemmaIndex] = None
        existing_source_counts = _meta_source_counts(meta)
        if (not existing_source_counts) and index_path.exists():
            existing_index = LemmaIndex.load(index_path)
            if existing_index is not None:
                existing_source_counts = _entry_source_counts(existing_index.entries)

        if resolved_roots.missing_required:
            missing_text = ", ".join(sorted(resolved_roots.missing_required))
            msg = (
                "LemmaRetriever: required retrieval roots unavailable "
                f"({missing_text}); lean.project_dir={self.lean_cfg.project_dir!r}, "
                f"project_root={self.cfg.project_root!r}. "
                "Project/support retrieval cannot load without a valid project root."
            )
            if self.cfg.update_on_start:
                raise RuntimeError(msg)
            logger.warning(
                "%s Retriever will remain unready until the project root is available.",
                msg,
            )
            self.index = None
            self._ready = False
            return

        need_rebuild = False
        force_rebuild = False
        rebuild_reasons: List[str] = []
        if not index_path.exists():
            need_rebuild = True
            force_rebuild = True
            rebuild_reasons.append("index_missing")
        elif not meta:
            need_rebuild = True
            force_rebuild = True
            rebuild_reasons.append("meta_missing")
        elif meta and meta.get("fingerprint") != fingerprint:
            need_rebuild = True
            force_rebuild = True
            rebuild_reasons.append("fingerprint_mismatch")
        elif meta and meta.get("config_fingerprint") != cfg_fp:
            need_rebuild = True
            force_rebuild = True
            rebuild_reasons.append("config_fingerprint_mismatch")

        if meta and not versions_match(meta, expected_versions):
            need_rebuild = True
            force_rebuild = True
            rebuild_reasons.append("artifact_version_mismatch")

        if int(existing_source_counts.get("mathlib", 0)) > 0:
            need_rebuild = True
            force_rebuild = True
            rebuild_reasons.append("mixed_support_index_deprecated")

        if need_rebuild and (self.cfg.update_on_start or force_rebuild):
            if rebuild_reasons:
                logger.info(
                    "Lemma index rebuild starting (%s)", ", ".join(rebuild_reasons)
                )
            else:
                logger.info("Lemma index rebuild starting...")
            idx = build_index(
                roots,
                max_lemmas=self.cfg.max_lemmas,
                include_docstrings=self.cfg.include_docstrings,
                file_paths=all_files,
            )
            new_source_counts = _entry_source_counts(idx.entries)

            # Guard: refuse to overwrite a non-empty index with an empty build.
            # This prevents cwd-resolution bugs from destroying a valid index.
            existing_count = meta.get("lemma_count", 0) if meta else 0
            if len(idx.entries) == 0 and existing_count > 0:
                logger.error(
                    "Lemma index rebuild produced 0 entries but existing index has %d. "
                    "Refusing to overwrite — likely a path resolution issue. "
                    "project_dir=%r, roots=%s. Loading existing index instead.",
                    existing_count,
                    self.lean_cfg.project_dir,
                    roots,
                )
                self.index = LemmaIndex.load(index_path)
                self._ready = self.index is not None
            else:
                meta_obj = LemmaIndexMeta(
                    created_ts=time.time(),
                    fingerprint=fingerprint,
                    file_count=len(all_files),
                    lemma_count=len(idx.entries),
                    config_fingerprint=cfg_fp,
                    source_counts=new_source_counts,
                    artifact_schema_version=int(
                        expected_versions["artifact_schema_version"]
                    ),
                    statement_parser_version=str(
                        expected_versions["statement_parser_version"]
                    ),
                )
                idx.save(index_path, meta_path, meta_obj)
                self.index = idx
                self._ready = True
                active_meta = dict(meta_obj.__dict__)
        else:
            self.index = LemmaIndex.load(index_path)
            self._ready = self.index is not None

        if self.index is not None:
            filtered_index = _project_only_index(self.index)
            if filtered_index is not self.index:
                logger.warning(
                    "LemmaRetriever: loaded support index still contained Mathlib entries; "
                    "dropping them from runtime state."
                )
                self.index = filtered_index
                self._ready = True

        if not self._ready:
            logger.warning(
                "LemmaRetriever: index not available. Run scripts/build_lemma_index.py to create it."
            )
            return

        if self.cfg.use_embeddings:
            backend = str(self.cfg.embedding_backend or "").strip().lower()
            if backend != "sentence_transformers":
                raise ValueError(
                    "LemmaRetriever requires sentence-transformer embeddings; "
                    f"got embedding_backend={self.cfg.embedding_backend!r}"
                )
            emb_cfg = EmbedderConfig(
                backend=self.cfg.embedding_backend,
                model=self.cfg.embedding_model,
                device=self.cfg.embedding_device,
                normalize=self.cfg.embedding_normalize,
                prefer_local_files=bool(
                    getattr(self.cfg, "embedding_prefer_local_files", True)
                ),
                local_files_only=bool(
                    getattr(self.cfg, "embedding_local_files_only", False)
                ),
                allow_download=bool(
                    getattr(self.cfg, "embedding_allow_download", True)
                ),
                init_timeout_s=float(
                    getattr(self.cfg, "embedding_init_timeout_s", 20.0)
                ),
                dim=self.cfg.embedding_dim,
                seed=self.cfg.embedding_seed,
            )
            try:
                self._embedder = make_embedder(emb_cfg)
                actual_dim = (
                    int(getattr(self._embedder, "dim", 0) or 0)
                    if self._embedder is not None
                    else 0
                )
                if actual_dim != int(self.cfg.embedding_dim):
                    raise ValueError(
                        "LemmaRetriever embedding dimension mismatch: "
                        f"config={self.cfg.embedding_dim}, embedder={actual_dim}"
                    )
                self._embedder_init_error = ""
                # Clear embedding caches when embedder changes to prevent dimension mismatches
                self._embedding_cache.clear()
                self._query_embedding_cache.clear()
                logger.debug("Embedding caches cleared after embedder initialization")
            except Exception as exc:
                logger.warning(
                    "LemmaRetriever: embedder init failed (%s); disabling embeddings.",
                    exc,
                )
                self._embedder_init_error = str(exc)
                self._embedder = None
                self.cfg.use_embeddings = False

        # Optional dense index for fast semantic retrieval.
        if self.cfg.dense_retrieval_enabled and self._embedder is not None:
            try:
                self._load_or_build_dense_index(meta_obj=active_meta, cfg_fp=cfg_fp)
            except Exception as exc:
                logger.warning(
                    "LemmaRetriever: dense index init failed (%s); disabling dense retrieval.",
                    exc,
                )
                self._dense_matrix = None
                self._dense_ready = False
                self.cfg.dense_retrieval_enabled = False

    def _dense_meta_payload(
        self, *, index_fingerprint: str, cfg_fp: str
    ) -> Dict[str, Any]:
        return stamp_versions(
            {
                "index_fingerprint": index_fingerprint,
                "config_fingerprint": cfg_fp,
                "embedding_backend": str(self.cfg.embedding_backend),
                "embedding_model": str(self.cfg.embedding_model),
                "embedding_device": (
                    str(self.cfg.embedding_device) if self.cfg.embedding_device else ""
                ),
                "embedding_normalize": bool(self.cfg.embedding_normalize),
                "embedding_dim": (
                    int(getattr(self._embedder, "dim", self.cfg.embedding_dim))
                    if self._embedder
                    else 0
                ),
                "embedding_seed": int(self.cfg.embedding_seed),
                "created_ts": time.time(),
            },
            current_lemma_index_versions(),
        )

    def _load_or_build_dense_index(
        self, *, meta_obj: Optional[Dict[str, Any]], cfg_fp: str
    ) -> None:
        """Load or build a dense (cosine-normalized) embedding matrix aligned to lemma index."""
        if not self.index or self._embedder is None:
            return
        dense_path = Path(self.cfg.dense_index_path)
        dense_meta_path = Path(self.cfg.dense_meta_path)
        expected_dim = int(getattr(self._embedder, "dim", self.cfg.embedding_dim) or 0)
        index_fingerprint = ""
        if isinstance(meta_obj, dict):
            index_fingerprint = str(meta_obj.get("fingerprint") or "")

        want_meta = self._dense_meta_payload(
            index_fingerprint=index_fingerprint, cfg_fp=cfg_fp
        )
        have_meta: Optional[Dict[str, Any]] = None
        if dense_meta_path.exists():
            try:
                have_meta = json.loads(dense_meta_path.read_text(encoding="utf-8"))
            except Exception as exc:
                logger.warning(
                    "_load_or_build_dense_index: failed to parse meta %s: %s",
                    dense_meta_path,
                    exc,
                )
                have_meta = None

        def _meta_matches() -> bool:
            if not have_meta:
                return False
            for k in (
                "index_fingerprint",
                "config_fingerprint",
                "embedding_backend",
                "embedding_model",
                "embedding_dim",
                "embedding_seed",
                "artifact_schema_version",
                "statement_parser_version",
            ):
                if str(have_meta.get(k, "")) != str(want_meta.get(k, "")):
                    return False
            return True

        loaded = False
        mismatch_note = ""
        force_rebuild = False
        expected_rows = len(self.index.entries)
        meta_matches = _meta_matches()
        if dense_path.exists() and not meta_matches:
            mismatch_note = "meta mismatch"
            force_rebuild = True
        elif not dense_path.exists() and dense_meta_path.exists():
            mismatch_note = "dense index missing"
            force_rebuild = True

        if dense_path.exists() and meta_matches:
            if np is not None:
                try:
                    arr = np.load(str(dense_path), mmap_mode="r")
                    if getattr(arr, "ndim", 0) == 2:
                        got_rows = int(arr.shape[0])
                        got_dim = int(arr.shape[1]) if int(arr.ndim) >= 2 else 0
                        if got_rows == expected_rows and got_dim == expected_dim:
                            self._dense_matrix = arr
                            loaded = True
                        elif got_rows != expected_rows:
                            mismatch_note = f"rows mismatch (expected {expected_rows}, got {got_rows})"
                        else:
                            mismatch_note = f"dimension mismatch (expected {expected_dim}, got {got_dim})"
                except Exception as exc:
                    logger.debug(
                        "Dense index npy load failed for %s: %s", dense_path, exc
                    )
                    loaded = False
            if not loaded:
                json_path = Path(str(dense_path) + ".json")
                if json_path.exists():
                    try:
                        mat = json.loads(json_path.read_text(encoding="utf-8"))
                        if isinstance(mat, list):
                            got_rows = len(mat)
                            dims_ok = all(
                                isinstance(row, list) and len(row) == expected_dim
                                for row in mat
                            )
                            if got_rows == expected_rows and dims_ok:
                                self._dense_matrix = mat
                                loaded = True
                            elif got_rows != expected_rows:
                                mismatch_note = f"rows mismatch (expected {expected_rows}, got {got_rows})"
                            else:
                                mismatch_note = (
                                    f"dimension mismatch (expected {expected_dim})"
                                )
                    except Exception as exc:
                        logger.debug(
                            "Dense index JSON fallback load failed for %s: %s",
                            json_path,
                            exc,
                        )
                        loaded = False
            if not loaded:
                force_rebuild = True
                if not mismatch_note:
                    mismatch_note = "dense index unreadable"

        if loaded:
            self._dense_ready = True
            return

        should_build = bool(self.cfg.dense_build_on_start) or bool(force_rebuild)
        if not should_build:
            self._dense_matrix = None
            self._dense_ready = False
            logger.info(
                "LemmaRetriever: dense retrieval enabled but dense index not usable%s. "
                "Set retrieval.dense_build_on_start=true to build it.",
                f" ({mismatch_note})" if mismatch_note else "",
            )
            return
        if force_rebuild and not self.cfg.dense_build_on_start:
            logger.info(
                "LemmaRetriever: forcing dense index rebuild despite dense_build_on_start=false (%s).",
                mismatch_note or "stale_dense_index",
            )

        entries = self.index.entries
        n = len(entries)
        if n == 0:
            self._dense_matrix = (
                np.zeros((0, 0), dtype=np.float32) if np is not None else []
            )
            self._dense_ready = True
            return

        def _embed_text(e: LemmaEntry) -> str:
            if self.cfg.include_docstrings and e.docstring:
                return f"{e.name} : {e.type}\n{e.docstring}"
            return f"{e.name} : {e.type}"

        batch_size = max(1, int(self.cfg.dense_build_batch_size))

        def embed_batch(texts: List[str]) -> List[List[float]]:
            """Bound one dense-build provider call without unsafe late writes."""

            timeout_s = max(
                0.1,
                float(
                    getattr(self.cfg, "dense_build_batch_timeout_s", 300.0)
                    or 300.0
                ),
            )
            if not _DENSE_EMBED_WORKER_SLOTS.acquire(blocking=False):
                raise RuntimeError("dense embedding worker capacity exhausted")
            done = threading.Event()
            box: Dict[str, Any] = {"vectors": None, "error": None}

            def worker() -> None:
                try:
                    box["vectors"] = self._embedder.embed_many(texts)
                except BaseException as exc:
                    box["error"] = exc
                finally:
                    _DENSE_EMBED_WORKER_SLOTS.release()
                    done.set()

            try:
                thread = threading.Thread(
                    target=worker,
                    name="mini-dense-embed-build",
                    daemon=True,
                )
                thread.start()
            except BaseException:
                _DENSE_EMBED_WORKER_SLOTS.release()
                raise
            if not done.wait(timeout=timeout_s):
                raise TimeoutError(
                    "dense embedding batch exceeded watchdog "
                    f"({timeout_s:.1f}s)"
                )
            error = box.get("error")
            if error is not None:
                raise error
            return list(box.get("vectors") or ())

        if np is not None:
            mat = None
            i = 0
            while i < n:
                chunk = entries[i : i + batch_size]
                texts = [_embed_text(e) for e in chunk]
                vecs = embed_batch(texts)

                if mat is None:
                    dim = len(vecs[0]) if vecs else 0
                    mat = np.empty((n, dim), dtype=np.float32)
                for j, v in enumerate(vecs):
                    mat[i + j] = np.asarray(v, dtype=np.float32)

                i += len(chunk)
                if i % 5000 == 0:
                    logger.info("Dense lemma index build: %d/%d", i, n)

            if mat is None:
                mat = np.zeros((0, 0), dtype=np.float32)
            norms = np.linalg.norm(mat, axis=1, keepdims=True)
            norms[norms == 0.0] = 1.0
            mat = mat / norms
            dense_path.parent.mkdir(parents=True, exist_ok=True)
            # NOTE: np.save appends ".npy" when the filename doesn't already end with it.
            # Use a temp suffix that ends with ".npy" so the file we write is the file we rename.
            fd, tmp = tempfile.mkstemp(dir=str(dense_path.parent), suffix=".tmp.npy")
            os.close(fd)
            try:
                np.save(tmp, mat.astype(np.float32, copy=False))
                Path(tmp).replace(dense_path)
            except BaseException:
                Path(tmp).unlink(missing_ok=True)
                raise
            self._dense_matrix = np.load(str(dense_path), mmap_mode="r")
        else:
            # Portability fallback: JSON matrix (slow to build/search for large N).
            mat_list: List[List[float]] = []
            i = 0
            while i < n:
                chunk = entries[i : i + batch_size]
                texts = [_embed_text(e) for e in chunk]
                vecs = embed_batch(texts)
                mat_list.extend(vecs)
                i += len(chunk)
                if i % 5000 == 0 and i > 0:
                    logger.info("Dense lemma index build (python): %d/%d", i, n)
            normed: List[List[float]] = []
            for v in mat_list:
                denom = math.sqrt(sum(x * x for x in v)) or 1.0
                normed.append([x / denom for x in v])
            json_path = Path(str(dense_path) + ".json")
            # Sanitize to prevent NaN/Infinity from corrupting JSON
            _atomic_write_text(json_path, json.dumps(_sanitize_for_json(normed)))
            self._dense_matrix = normed

        # Sanitize metadata as well
        _atomic_write_text(
            dense_meta_path, json.dumps(_sanitize_for_json(want_meta), sort_keys=True)
        )
        self._dense_ready = True
        logger.info("LemmaRetriever: dense lemma index built (%d entries)", n)

    def _dense_search(
        self,
        query_emb: List[float],
        top_k: int,
        *,
        allowed_doc_ids: Optional[set[int]] = None,
    ) -> List[Tuple[int, float]]:
        if self._dense_matrix is None or not self.index or top_k <= 0:
            return []
        denom = math.sqrt(sum(x * x for x in query_emb)) or 1.0
        q = [x / denom for x in query_emb]

        if np is not None and isinstance(self._dense_matrix, np.ndarray):
            if (
                getattr(self._dense_matrix, "ndim", 0) != 2
                or int(self._dense_matrix.shape[0]) == 0
            ):
                return []
            qv = np.asarray(q, dtype=np.float32)
            if qv.ndim != 1 or qv.shape[0] != self._dense_matrix.shape[1]:
                return []
            if allowed_doc_ids is not None:
                allowed = np.asarray(
                    sorted(
                        i
                        for i in allowed_doc_ids
                        if 0 <= int(i) < int(self._dense_matrix.shape[0])
                    ),
                    dtype=np.int64,
                )
                if int(allowed.size) == 0:
                    return []
                sims = self._dense_matrix[allowed] @ qv
                n = int(sims.shape[0])
            else:
                sims = self._dense_matrix @ qv
                allowed = None
                n = int(sims.shape[0])
            k = min(int(top_k), n)
            if k <= 0:
                return []
            if k == n:
                idxs = np.argsort(-sims)
            else:
                idxs = np.argpartition(-sims, k - 1)[:k]
                idxs = idxs[np.argsort(-sims[idxs])]
            if allowed is not None:
                return [(int(allowed[int(i)]), float(sims[int(i)])) for i in idxs]
            return [(int(i), float(sims[int(i)])) for i in idxs]

        if not isinstance(self._dense_matrix, list) or not self._dense_matrix:
            return []
        # Validate dimension consistency with dense matrix (list fallback path)
        query_dim = len(q)
        if self._dense_matrix and len(self._dense_matrix[0]) != query_dim:
            logger.warning(
                "Dense matrix dimension %d != query dimension %d; skipping dense scan",
                len(self._dense_matrix[0]),
                query_dim,
            )
            return []
        scored: List[Tuple[int, float]] = []
        row_iter: Iterable[Tuple[int, Any]]
        if allowed_doc_ids is None:
            row_iter = enumerate(self._dense_matrix)
        else:
            row_iter = (
                (i, self._dense_matrix[i])
                for i in sorted(allowed_doc_ids)
                if 0 <= int(i) < len(self._dense_matrix)
            )
        for i, v in row_iter:
            if not isinstance(v, list) or len(v) != query_dim:
                logger.warning(
                    "Dense matrix row %d is malformed; skipping dense scan", int(i)
                )
                return []
            try:
                scored.append((i, _cosine_sim(q, v)))
            except ValueError:
                logger.warning(
                    "Dense matrix row %d dimension mismatch; skipping dense scan",
                    int(i),
                )
                return []
        scored.sort(key=lambda x: x[1], reverse=True)
        return scored[:top_k]

    def _build_query_text(
        self, statement: str, *, goal_state: Optional[str] = None
    ) -> str:
        stmt = (statement or "").strip()
        if not stmt:
            return ""
        if self.cfg.goal_conditioned and goal_state and goal_state.strip():
            w = max(0.0, float(self.cfg.goal_query_weight))
            if w <= 1e-6:
                return stmt
            reps = max(1, min(3, int(round(w))))
            gs = goal_state.strip()
            return stmt + "\n\n" + "\n".join([gs] * reps)
        return stmt

    def _cache_embedding(self, doc_id: int, emb: List[float]) -> None:
        if self._embedding_cache_size <= 0:
            return
        self._embedding_cache[doc_id] = emb
        self._embedding_cache.move_to_end(doc_id)
        if len(self._embedding_cache) > self._embedding_cache_size:
            self._embedding_cache.popitem(last=False)

    def _cache_query_embedding(self, query_text: str, emb: List[float]) -> None:
        if self._query_embedding_cache_size <= 0:
            return
        key = (query_text or "").strip()
        if not key:
            return
        self._query_embedding_cache[key] = emb
        self._query_embedding_cache.move_to_end(key)
        if len(self._query_embedding_cache) > self._query_embedding_cache_size:
            self._query_embedding_cache.popitem(last=False)

    def _get_query_embedding(
        self,
        query_text: str,
        *,
        deadline_safe: bool = False,
        deadline_monotonic: Optional[float] = None,
    ) -> Optional[List[float]]:
        if self._embedder is None:
            return None
        key = (query_text or "").strip()
        if not key:
            return None
        cached = self._query_embedding_cache.get(key)
        if cached is not None:
            # refresh LRU
            self._query_embedding_cache.move_to_end(key)
            return cached
        if deadline_safe:
            remaining_s = (
                max(0.01, float(deadline_monotonic) - time.monotonic())
                if deadline_monotonic is not None
                else None
            )
            vectors = _online_embed_many_with_watchdog(
                self._embedder,
                [key],
                timeout_s=remaining_s,
            )
            emb = list(vectors[0]) if vectors else []
        else:
            emb = self._embedder.embed(key)
        if not emb:
            return None
        self._cache_query_embedding(key, emb)
        return emb

    def _cross_encoder_key(self, query: str, entry: LemmaEntry) -> str:
        # Keep cache keys small and deterministic.
        # Include model mode so fallback transitions don't serve stale scores.
        mode = (
            "llm"
            if self._cross_encoder_is_llm
            else ("cpu" if self._cross_encoder_force_cpu_fallback else "layerwise")
        )
        # L7 fix: use \0 separator to avoid collisions when query contains newlines.
        payload = (mode + "\0" + query + "\0" + entry.name + "\0" + entry.type).encode(
            "utf-8"
        )
        return hashlib.sha1(payload).hexdigest()

    def _cache_cross_score(self, key: str, score: float) -> None:
        if self._cross_encoder_cache_size <= 0:
            return
        self._cross_encoder_cache[key] = float(score)
        self._cross_encoder_cache.move_to_end(key)
        if len(self._cross_encoder_cache) > self._cross_encoder_cache_size:
            self._cross_encoder_cache.popitem(last=False)

    # ---- LTR (learning-to-rank) -----------------------------------------

    def _ltr_default_weights(self) -> Dict[str, float]:
        return {
            "bm25_norm": float(self.cfg.weight_bm25),
            "symbol": float(self.cfg.weight_symbol),
            "name": float(self.cfg.weight_name),
            "dense": float(self.cfg.weight_embed),
            # Rank and rerank are auxiliary signals; start small.
            "rank": 0.1,
            "rerank": 0.2,
        }

    def _ltr_load(self) -> None:
        path = Path(self.cfg.ltr_weights_path)
        if not path.exists():
            self._ltr_weights = self._ltr_default_weights()
            self._ltr_bias = 0.0
            self._ltr_updates = 0
            return
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
            weights = data.get("weights", {})
            if isinstance(weights, dict):
                # Clamp loaded weights to prevent sigmoid saturation
                self._ltr_weights = {
                    k: max(-10.0, min(10.0, float(v))) for k, v in weights.items()
                }
            else:
                self._ltr_weights = self._ltr_default_weights()
            # Clamp loaded bias to prevent sigmoid saturation
            self._ltr_bias = max(-10.0, min(10.0, float(data.get("bias", 0.0))))
            self._ltr_updates = int(data.get("updates", 0))
        except Exception as exc:
            logger.warning(
                "_ltr_load: failed to parse %s, using defaults: %s", path, exc
            )
            self._ltr_weights = self._ltr_default_weights()
            self._ltr_bias = 0.0
            self._ltr_updates = 0

    def _ltr_save(self) -> None:
        path = Path(self.cfg.ltr_weights_path)
        try:
            payload = {
                "weights": self._ltr_weights,
                "bias": self._ltr_bias,
                "updates": self._ltr_updates,
            }
            # Sanitize to prevent NaN/Infinity from corrupting JSON
            _atomic_write_text(
                path, json.dumps(_sanitize_for_json(payload), sort_keys=True)
            )
        except Exception as exc:
            # Log at WARNING so learning data loss is visible
            logger.warning("LTR weights save failed: %s", exc)

    def _ltr_score(self, feats: Dict[str, float]) -> float:
        # Clamp features to [0,1] for stability.
        s = float(self._ltr_bias)
        for k in self._ltr_feature_names:
            v = float(feats.get(k, 0.0))
            v = max(0.0, min(1.0, v))
            w = float(self._ltr_weights.get(k, 0.0))
            s += w * v
        return _math_sigmoid(s)

    def get_last_rerank_scores(self) -> Dict[str, float]:
        return dict(self._last_rerank_scores or {})

    def rerank_with_ltr(
        self,
        entries: List[LemmaEntry],
        feature_map: Optional[Dict[str, Dict[str, float]]],
    ) -> List[LemmaEntry]:
        """Re-rank lemmas using online LTR weights (if enabled)."""
        if not entries or not self._ltr_enabled or not feature_map:
            return entries
        min_updates = int(self.cfg.ltr_min_updates)
        if self._ltr_updates < min_updates:
            return entries
        warmup = int(self.cfg.ltr_warmup_updates)
        alpha = 1.0 if warmup <= 0 else min(1.0, self._ltr_updates / max(1, warmup))

        scored: List[Tuple[float, int, LemmaEntry]] = []
        n = len(entries)
        for rank, e in enumerate(entries):
            feats = dict(feature_map.get(e.name, {}))
            # Inject current rank feature (post-rerank order).
            rank_norm = 1.0 - (rank / max(1, n - 1))
            feats["rank"] = max(0.0, min(1.0, rank_norm))
            base = float(feats.get("base_score", 0.0))
            base = max(0.0, min(1.0, base))
            ltr_score = self._ltr_score(feats)
            final = (1.0 - alpha) * base + alpha * ltr_score
            scored.append((final, rank, e))
        scored.sort(key=lambda x: x[0], reverse=True)
        return [e for _, _, e in scored]

    def update_ltr(
        self,
        used_lemmas: List[str],
        feature_map: Optional[Dict[str, Dict[str, float]]],
    ) -> None:
        """Online update of LTR weights from a successful proof."""
        if not self._ltr_enabled or not feature_map or not used_lemmas:
            return
        pos = [n for n in used_lemmas if n in feature_map]
        if not pos:
            return

        neg_candidates = [n for n in feature_map.keys() if n not in pos]
        neg_limit = int(self.cfg.ltr_negative_samples)
        if neg_limit > 0 and len(neg_candidates) > neg_limit:
            rng = random.Random(self.cfg.embedding_seed + self._ltr_updates)
            neg = rng.sample(neg_candidates, neg_limit)
        else:
            neg = neg_candidates

        lr = float(self.cfg.ltr_learning_rate)
        pos_w = float(self.cfg.ltr_positive_weight)
        decay = float(self.cfg.ltr_weight_decay)

        examples = [(n, 1.0) for n in pos] + [(n, 0.0) for n in neg]
        for name, y in examples:
            feats = feature_map.get(name, {})
            # Build feature vector with clamped values.
            x: Dict[str, float] = {}
            for k in self._ltr_feature_names:
                v = float(feats.get(k, 0.0))
                x[k] = max(0.0, min(1.0, v))
            pred = self._ltr_score(x)
            weight = pos_w if y > 0 else 1.0
            grad = (y - pred) * weight
            for k, v in x.items():
                self._ltr_weights[k] = (
                    float(self._ltr_weights.get(k, 0.0)) + lr * grad * v
                )
            self._ltr_bias += lr * grad

        # Clamp weights and bias to prevent sigmoid saturation.
        # Without clamping, bias can grow to 100+ causing sigmoid(x) ≈ 1.0 always.
        for k in list(self._ltr_weights.keys()):
            self._ltr_weights[k] = max(-10.0, min(10.0, self._ltr_weights[k]))
        self._ltr_bias = max(-10.0, min(10.0, self._ltr_bias))

        if decay < 1.0:
            for k in list(self._ltr_weights.keys()):
                self._ltr_weights[k] *= decay
            self._ltr_bias *= decay

        self._ltr_updates += 1
        self._ltr_save()

    def _score_candidates(
        self,
        statement: str,
        goal_state: Optional[str],
        domain_hint: Optional[DomainHint],
        top_k: int,
        exclude: Optional[set[str]] = None,
        exclude_sources: Optional[set[str]] = None,
        deadline_exhausted: Optional[Callable[[], bool]] = None,
        deadline_monotonic: Optional[float] = None,
    ) -> List[Tuple[float, LemmaEntry, Dict[str, float]]]:
        if not self.index:
            return []
        exclude = exclude or set()
        idx = self.index

        def deadline_elapsed() -> bool:
            if (
                deadline_monotonic is not None
                and time.monotonic() >= float(deadline_monotonic)
            ):
                return True
            try:
                return bool(deadline_exhausted and deadline_exhausted())
            except Exception:
                return True

        def _allowed(doc_id: int) -> bool:
            entry = idx.entries[doc_id]
            if entry.name in exclude:
                return False
            if exclude_sources and entry.source in exclude_sources:
                return False
            return True

        query_text = self._build_query_text(statement, goal_state=goal_state)
        query_tokens = _tokenize(query_text)
        query_syms = set(_extract_symbols(query_text))

        # BM25 via inverted index
        scores: Dict[int, float] = {}
        k1 = self.cfg.bm25_k1
        b = self.cfg.bm25_b
        avg_len = max(1.0, idx.avg_len)
        for tok in query_tokens:
            if deadline_elapsed():
                break
            postings = idx.inv_index.get(tok)
            if not postings:
                continue
            idf = idx.idf.get(tok, 0.0)
            for doc_id, tf in postings:
                if deadline_elapsed():
                    break
                dl = idx.doc_len[doc_id]
                denom = tf + k1 * (1.0 - b + b * (dl / avg_len))
                score = idf * ((tf * (k1 + 1.0)) / max(1e-6, denom))
                scores[doc_id] = scores.get(doc_id, 0.0) + score

        have_dense = bool(
            self.cfg.dense_retrieval_enabled
            and self._dense_ready
            and self._dense_matrix is not None
            and self._embedder is not None
        )
        allow_embedding_fallback = bool(
            self._embedder is not None and self.cfg.use_embeddings
        )
        if not scores and not have_dense and not allow_embedding_fallback:
            return []

        # Candidate pool: BM25 top + optional dense top (hybrid retrieval).
        pool_mult = max(1, int(self.cfg.hybrid_pool_multiplier))
        pool_size = max(top_k, min(len(scores), top_k * pool_mult)) if scores else 0
        bm25_top: List[Tuple[int, float]] = []
        if scores:
            for doc_id, score in sorted(
                scores.items(), key=lambda x: x[1], reverse=True
            ):
                if not _allowed(doc_id):
                    continue
                bm25_top.append((doc_id, score))
                if len(bm25_top) >= pool_size:
                    break
        bm25_map: Dict[int, float] = {doc_id: s for doc_id, s in bm25_top}
        bm25_max = max(bm25_map.values(), default=0.0)
        if bm25_max <= 1e-9:
            bm25_max = 1.0

        dense_map: Dict[int, float] = {}
        allowed_doc_ids: Optional[set[int]] = None
        if exclude or exclude_sources:
            allowed_doc_ids = {i for i in range(len(idx.entries)) if _allowed(i)}
        if have_dense and self._embedder is not None and not deadline_elapsed():
            try:
                qemb = self._get_query_embedding(
                    query_text,
                    deadline_safe=True,
                    deadline_monotonic=deadline_monotonic,
                )
            except Exception as exc:
                logger.debug("Dense query embedding unavailable: %s", exc)
                qemb = None
            dtop = int(self.cfg.dense_top_k)
            mode = (self.cfg.dense_search_mode or "full").strip().lower()
            # Fast path: only score the BM25 candidate pool (avoids full-matrix multiply).
            if qemb is not None and (
                mode == "bm25_filtered"
                and bm25_top
                and np is not None
                and isinstance(self._dense_matrix, np.ndarray)
            ):
                doc_ids = [int(doc_id) for doc_id, _ in bm25_top]
                denom = math.sqrt(sum(x * x for x in qemb)) or 1.0
                qv = np.asarray([x / denom for x in qemb], dtype=np.float32)
                try:
                    sub = self._dense_matrix[doc_ids]
                    if getattr(sub, "ndim", 0) == 2 and int(sub.shape[1]) == int(
                        qv.shape[0]
                    ):
                        sims = sub @ qv
                        k = min(int(dtop), int(sims.shape[0]))
                        if k > 0:
                            if k == int(sims.shape[0]):
                                idxs = np.argsort(-sims)
                            else:
                                idxs = np.argpartition(-sims, k - 1)[:k]
                                idxs = idxs[np.argsort(-sims[idxs])]
                            for j in idxs:
                                did = doc_ids[int(j)]
                                dense_map[did] = float(sims[int(j)])
                except Exception as exc:
                    logger.debug(
                        "BM25-guided dense lookup failed, falling back to full dense search: %s",
                        exc,
                    )
                    for doc_id, sim in self._dense_search(
                        qemb, dtop, allowed_doc_ids=allowed_doc_ids
                    ):
                        dense_map[int(doc_id)] = float(sim)
            elif qemb is not None:
                for doc_id, sim in self._dense_search(
                    qemb, dtop, allowed_doc_ids=allowed_doc_ids
                ):
                    dense_map[int(doc_id)] = float(sim)

        candidate_ids: List[int] = []
        seen_ids: set[int] = set()
        for doc_id, _ in bm25_top:
            if doc_id not in seen_ids:
                candidate_ids.append(doc_id)
                seen_ids.add(doc_id)
        for doc_id, _ in sorted(dense_map.items(), key=lambda x: x[1], reverse=True):
            if doc_id not in seen_ids:
                candidate_ids.append(doc_id)
                seen_ids.add(doc_id)

        if allow_embedding_fallback and not dense_map and not deadline_elapsed():
            # Without a dense artifact, semantic scoring is an online
            # fallback.  Bound that fallback: embedding an entire project one
            # declaration at a time made the default 1k-entry project source
            # exceed Mini's 30s retrieval watchdog on every cold query.
            # Full-corpus semantic recall belongs to the persistent dense
            # index; this lane reranks a deterministic bounded corpus prefix
            # plus the BM25 shortlist.
            fallback_cap = max(64, int(top_k or 1))
            candidate_ids = candidate_ids[:fallback_cap]
            seen_ids = set(candidate_ids)
            fallback_doc_ids = (
                sorted(allowed_doc_ids)
                if allowed_doc_ids is not None
                else list(range(len(idx.entries)))
            )[:fallback_cap]
            for doc_id in fallback_doc_ids:
                if len(candidate_ids) >= fallback_cap:
                    break
                if doc_id not in seen_ids:
                    candidate_ids.append(doc_id)
                    seen_ids.add(doc_id)

        if not candidate_ids:
            return []

        # Optional embedding similarity (fallback if no dense index)
        query_emb: Optional[List[float]] = None
        if allow_embedding_fallback and not dense_map and not deadline_elapsed():
            try:
                query_emb = self._get_query_embedding(
                    query_text,
                    deadline_safe=True,
                    deadline_monotonic=deadline_monotonic,
                )
            except Exception as exc:
                logger.debug("Online query embedding unavailable: %s", exc)
                query_emb = None

        fallback_embeddings: Dict[int, List[float]] = {}
        if query_emb is not None and self._embedder is not None:
            missing_doc_ids: List[int] = []
            missing_texts: List[str] = []
            for doc_id in candidate_ids:
                cached = self._embedding_cache.get(doc_id)
                if cached is not None and len(cached) == len(query_emb):
                    fallback_embeddings[doc_id] = cached
                    move_to_end = getattr(self._embedding_cache, "move_to_end", None)
                    if callable(move_to_end):
                        move_to_end(doc_id)
                    continue
                if cached is not None:
                    self._embedding_cache.pop(doc_id, None)
                entry = idx.entries[doc_id]
                missing_doc_ids.append(doc_id)
                missing_texts.append(f"{entry.name} : {entry.type}")
            if missing_doc_ids and not deadline_elapsed():
                try:
                    vectors = _online_embed_many_with_watchdog(
                        self._embedder,
                        missing_texts,
                        timeout_s=(
                            max(
                                0.01,
                                float(deadline_monotonic) - time.monotonic(),
                            )
                            if deadline_monotonic is not None
                            else None
                        ),
                    )
                except Exception as exc:
                    logger.debug("Online embedding batch failed: %s", exc)
                    vectors = []
                    # Preserve lexical/BM25 retrieval when the optional
                    # semantic reranker is unavailable or times out.
                    query_emb = None
                if query_emb is not None:
                    if len(vectors) != len(missing_doc_ids):
                        logger.debug(
                            "Online embedding batch cardinality mismatch: expected %d, got %d; "
                            "missing candidates will use lexical scoring",
                            len(missing_doc_ids),
                            len(vectors),
                        )
                    for doc_id, vector in zip(missing_doc_ids, vectors):
                        candidate = list(vector or [])
                        if len(candidate) != len(query_emb):
                            continue
                        fallback_embeddings[doc_id] = candidate
                        self._cache_embedding(doc_id, candidate)

        results: List[Tuple[float, LemmaEntry, Dict[str, float]]] = []
        for doc_id in candidate_ids:
            if deadline_elapsed():
                break
            bm25 = bm25_map.get(doc_id, 0.0)
            entry = idx.entries[doc_id]
            if entry.name in exclude:
                continue
            if exclude_sources and entry.source in exclude_sources:
                continue
            # Symbol overlap
            sym = 0.0
            if query_syms and idx.symbols[doc_id]:
                sym = len(query_syms.intersection(idx.symbols[doc_id])) / max(
                    1.0, len(query_syms)
                )

            # Name overlap
            name_overlap = 0.0
            name_tokens = idx.name_tokens[doc_id]
            if name_tokens:
                qset = set(query_tokens)
                name_overlap = len(qset.intersection(name_tokens)) / max(
                    1.0, len(set(name_tokens))
                )

            # Dense similarity or fallback embedding similarity.
            emb_score = 0.0
            if dense_map:
                emb_score = max(0.0, float(dense_map.get(doc_id, 0.0)))
            elif query_emb is not None and self._embedder is not None:
                cand_emb = fallback_embeddings.get(doc_id)
                if cand_emb is not None:
                    emb_score = max(0.0, _cosine_sim(query_emb, cand_emb))

            bm25_norm = max(0.0, bm25) / bm25_max
            score = (
                self.cfg.weight_bm25 * bm25_norm
                + self.cfg.weight_symbol * sym
                + self.cfg.weight_name * name_overlap
                + self.cfg.weight_embed * emb_score
            )

            # Domain prefix boost
            if domain_hint and domain_hint.useful_lemma_prefixes:
                for pref in domain_hint.useful_lemma_prefixes:
                    if entry.name.startswith(pref) or f".{pref}" in entry.name:
                        score *= self.cfg.boost_domain_prefix
                        break

            results.append(
                (
                    score,
                    entry,
                    {
                        "bm25": bm25,
                        "bm25_norm": bm25_norm,
                        "symbol": sym,
                        "name": name_overlap,
                        "dense": emb_score,
                    },
                )
            )

        results.sort(key=lambda x: x[0], reverse=True)
        return results[:top_k]

    def _extract_local_decls(self, preamble: str) -> List[LemmaEntry]:
        if not preamble.strip():
            return []
        try:
            entries = _scan_file(preamble, Path("<preamble>"))
        except Exception as exc:
            logger.debug("_extract_local_decls: preamble scan failed: %s", exc)
            return []
        for e in entries:
            e.source = "local"
        return entries

    def extract_local_decls(self, preamble: str) -> List[LemmaEntry]:
        """Public wrapper for prompt-local declaration extraction."""
        return self._extract_local_decls(preamble)

    def retrieve(
        self,
        statement: str,
        *,
        preamble: str = "",
        domain_hint: Optional[DomainHint] = None,
        exclude: Optional[set[str]] = None,
        exclude_sources: Optional[set[str]] = None,
        goal_state: Optional[str] = None,
        max_results: Optional[int] = None,
        deadline_exhausted: Optional[Callable[[], bool]] = None,
        deadline_monotonic: Optional[float] = None,
    ) -> Tuple[List[LemmaEntry], List[LemmaEntry]]:
        local = self._extract_local_decls(preamble)
        if not self._ready or not self.index:
            return local, []
        exclude = exclude or set()
        local_names = {e.name for e in local}
        exclude = exclude.union(local_names)
        limit = (
            int(max_results)
            if max_results is not None
            else int(self.cfg.max_prompt_lemmas)
        )
        limit = max(1, limit)
        score_limit = max(1, max(int(self.cfg.top_k), limit))

        ranked = self._score_candidates(
            statement,
            goal_state,
            domain_hint,
            score_limit,
            exclude=exclude,
            exclude_sources=exclude_sources,
            deadline_exhausted=deadline_exhausted,
            deadline_monotonic=deadline_monotonic,
        )
        # Apply minimum score threshold
        filtered = [e for s, e, _ in ranked if s >= self.cfg.min_score]
        return local, filtered[:limit]

    def retrieve_with_scores(
        self,
        statement: str,
        *,
        preamble: str = "",
        domain_hint: Optional[DomainHint] = None,
        exclude: Optional[set[str]] = None,
        exclude_sources: Optional[set[str]] = None,
        goal_state: Optional[str] = None,
        max_results: Optional[int] = None,
        deadline_exhausted: Optional[Callable[[], bool]] = None,
        deadline_monotonic: Optional[float] = None,
    ) -> Tuple[List[LemmaEntry], List[Tuple[LemmaEntry, float, Dict[str, float]]]]:
        local = self._extract_local_decls(preamble)
        if not self._ready or not self.index:
            return local, []
        exclude = exclude or set()
        local_names = {e.name for e in local}
        exclude = exclude.union(local_names)
        limit = (
            int(max_results)
            if max_results is not None
            else int(self.cfg.max_prompt_lemmas)
        )
        limit = max(1, limit)
        score_limit = max(1, max(int(self.cfg.top_k), limit))

        ranked = self._score_candidates(
            statement,
            goal_state,
            domain_hint,
            score_limit,
            exclude=exclude,
            exclude_sources=exclude_sources,
            deadline_exhausted=deadline_exhausted,
            deadline_monotonic=deadline_monotonic,
        )
        filtered: List[Tuple[LemmaEntry, float, Dict[str, float]]] = []
        for score, entry, details in ranked:
            if score >= self.cfg.min_score:
                filtered.append((entry, score, details))
            if len(filtered) >= limit:
                break
        return local, filtered

    def _lemma_line(self, e: LemmaEntry) -> str:
        if e.docstring and self.cfg.include_docstrings:
            return f"{e.name} : {e.type}  -- {e.docstring}"
        return f"{e.name} : {e.type}"

    def _budget_for_prompt(
        self,
        entries: List[LemmaEntry],
        statement: str,
        *,
        goal_state: Optional[str],
        token_budget: int,
    ) -> List[LemmaEntry]:
        """Select a diverse, de-duplicated subset of lemmas under a token budget."""
        if not entries:
            return []
        if not self.cfg.prompt_budget_enabled or token_budget <= 0:
            hard_cap = int(getattr(self.cfg, "prompt_budget_hard_cap_tokens", 0))
            if hard_cap <= 0:
                return entries
            token_budget = hard_cap

        max_items = int(self.cfg.max_prompt_lemmas)
        dedup_thr = float(self.cfg.prompt_budget_dedup_jaccard)
        query_text = self._build_query_text(statement, goal_state=goal_state)
        q_tokens = set(_tokenize(query_text))
        q_syms = set(_extract_symbols(query_text))

        selected: List[LemmaEntry] = []
        used_tokens: set[str] = set()
        used_syms: set[str] = set()
        used_types: List[str] = []
        used_namespaces: set[str] = set()
        budget_left = int(token_budget)

        for rank, e in enumerate(entries):
            if len(selected) >= max_items:
                break
            line = self._lemma_line(e)
            cost = _estimate_tokens(line, model=self._tokenizer_model)
            if cost <= 0 or cost > budget_left:
                continue

            typ_norm = _normalize_stmt(e.type)
            if typ_norm and any(_jaccard(typ_norm, t) >= dedup_thr for t in used_types):
                continue

            etoks = set(_tokenize(f"{e.name} {e.type}"))
            esyms = set(_extract_symbols(e.type))
            new_tok = len((etoks & q_tokens) - used_tokens)
            new_sym = len((esyms & q_syms) - used_syms)

            ns = (e.namespace or "").split(".")[0] if e.namespace else ""
            ns_pen = 0.25 if (ns and ns in used_namespaces) else 0.0

            # Rank prior (higher earlier); gain encourages coverage/diversity.
            prior = 1.0 - (rank / max(1.0, float(len(entries))))
            gain = (1.0 + 0.25 * float(new_tok) + 0.5 * float(new_sym)) * (1.0 - ns_pen)

            # If gain is tiny, skip once we already have a decent seed set.
            if gain < 1.05 and len(selected) >= max(3, max_items // 4):
                continue

            # Prefer keeping higher-prior items if budget is tight.
            if prior < 0.10 and budget_left < token_budget * 0.25:
                continue

            selected.append(e)
            budget_left -= cost
            used_tokens |= etoks & q_tokens
            used_syms |= esyms & q_syms
            if typ_norm:
                used_types.append(typ_norm)
            if ns:
                used_namespaces.add(ns)

        if not selected:
            fallback: List[LemmaEntry] = []
            fallback_budget = int(token_budget)
            fallback_cap = min(max_items, 3)
            for e in entries:
                if len(fallback) >= fallback_cap:
                    break
                cost = _estimate_tokens(
                    self._lemma_line(e), model=self._tokenizer_model
                )
                if cost <= 0 or cost > fallback_budget:
                    continue
                fallback.append(e)
                fallback_budget -= cost
            return fallback
        return selected

    def budget_for_prompt(
        self,
        entries: List[LemmaEntry],
        statement: str,
        *,
        goal_state: Optional[str] = None,
        token_budget: Optional[int] = None,
    ) -> List[LemmaEntry]:
        """Public wrapper for prompt budgeting using configured defaults."""
        budget = int(
            token_budget if token_budget is not None else self.cfg.prompt_budget_tokens
        )
        return self._budget_for_prompt(
            entries, statement, goal_state=goal_state, token_budget=budget
        )

    def rerank_with_cross_encoder(
        self,
        entries: List[LemmaEntry],
        statement: str,
        *,
        goal_state: Optional[str] = None,
        top_n: Optional[int] = None,
        force: bool = False,
    ) -> List[LemmaEntry]:
        """Optional cross-encoder reranker (requires sentence-transformers)."""
        if not entries:
            return entries
        self._last_rerank_scores = {}
        if (not force) and (self.cfg.rerank_mode or "none") != "cross_encoder":
            return entries
        if self._cross_encoder_is_temporarily_disabled():
            return entries
        n = int(top_n if top_n is not None else self.cfg.rerank_top_n)
        if n <= 0:
            return entries
        try:
            if self._cross_encoder is None:
                self._cross_encoder_is_llm = False
                force_st = bool(
                    getattr(
                        self.cfg, "cross_encoder_force_sentence_transformers", False
                    )
                )
                if self._cross_encoder_layerwise_disabled:
                    force_st = True
                llm_exc: Optional[BaseException] = None
                # Try LLM-based reranker first (minicpm-layerwise), unless explicitly forced off.
                if not force_st:
                    try:
                        use_fp16 = getattr(self.cfg, "cross_encoder_use_fp16", True)
                        llm_model, llm_exc = self._load_layerwise_reranker_with_timeout(
                            self.cfg.cross_encoder_model,
                            use_fp16=use_fp16,
                            device=self.cfg.cross_encoder_device,
                        )
                        if llm_exc is not None:
                            raise llm_exc
                        self._cross_encoder = llm_model
                        self._cross_encoder_is_llm = True
                        self._cross_encoder_cutoff_layers = getattr(
                            self.cfg, "cross_encoder_cutoff_layers", [28]
                        )
                        logger.info(
                            "Loaded LLM reranker: %s (layers=%s)",
                            self.cfg.cross_encoder_model,
                            self._cross_encoder_cutoff_layers,
                        )
                    except Exception as exc:
                        llm_exc = exc
                else:
                    if bool(
                        getattr(
                            self.cfg, "cross_encoder_force_sentence_transformers", False
                        )
                    ):
                        logger.info(
                            "cross_encoder_force_sentence_transformers=true: "
                            "skipping layerwise reranker and loading fallback CrossEncoder."
                        )
                    elif self._cross_encoder_layerwise_disabled:
                        logger.warning(
                            "Layerwise reranker disabled for this run (%s); "
                            "loading fallback CrossEncoder.",
                            self._cross_encoder_layerwise_disable_reason
                            or "runtime instability",
                        )

                if self._cross_encoder is None:
                    # Fall back to standard CrossEncoder (bge-reranker-large or configured fallback)
                    if llm_exc is not None:
                        _msg = str(llm_exc)
                        if (
                            isinstance(llm_exc, ModuleNotFoundError)
                            and "FlagEmbedding" in _msg
                        ):
                            logger.warning(
                                "Layerwise reranker unavailable: FlagEmbedding is not installed. "
                                "Install it in the active venv to use %s; using fallback CrossEncoder.",
                                self.cfg.cross_encoder_model,
                            )
                        elif "is_torch_fx_available" in _msg and "transformers" in _msg:
                            logger.warning(
                                "Layerwise reranker unavailable due to FlagEmbedding/transformers mismatch "
                                "(ImportError: %s). In practice this means transformers is too new for "
                                "the installed FlagEmbedding. Using fallback CrossEncoder.",
                                _msg,
                            )
                        else:
                            logger.info(
                                "LLM reranker unavailable (%s); trying fallback CrossEncoder.",
                                llm_exc,
                            )
                    try:
                        fallback_model = getattr(
                            self.cfg,
                            "cross_encoder_fallback_model",
                            "BAAI/bge-reranker-large",
                        )
                        dev = self.cfg.cross_encoder_device
                        if self._cross_encoder_force_cpu_fallback:
                            dev = "cpu"
                        ce_model, ce_exc = self._load_cross_encoder_with_timeout(
                            fallback_model,
                            device=dev,
                        )
                        if (
                            ce_exc is not None
                            and not self._cross_encoder_force_cpu_fallback
                            and str(dev or "").lower() != "cpu"
                        ):
                            self._cross_encoder_force_cpu_fallback = True
                            logger.warning(
                                "Cross-encoder load on %s failed (%s); retrying once on CPU.",
                                dev,
                                ce_exc,
                            )
                            ce_model, ce_exc = self._load_cross_encoder_with_timeout(
                                fallback_model,
                                device="cpu",
                            )
                        if ce_exc is not None:
                            raise ce_exc
                        self._cross_encoder = ce_model
                        self._mark_cross_encoder_success()
                        logger.info("Loaded fallback CrossEncoder: %s", fallback_model)
                    except Exception as fallback_exc:
                        logger.warning(
                            "Fallback CrossEncoder also failed (%s); reranking disabled.",
                            fallback_exc,
                        )
                        disable_kind = self._classify_cross_encoder_failure(
                            fallback_exc, stage="load"
                        )
                        self._disable_cross_encoder(
                            f"fallback_load_failed: {fallback_exc}",
                            kind=disable_kind,
                        )
                        return entries
                else:
                    self._mark_cross_encoder_success()
        except Exception as exc:
            logger.warning("Cross-encoder reranker unavailable (%s); skipping.", exc)
            disable_kind = self._classify_cross_encoder_failure(exc, stage="load")
            self._disable_cross_encoder(
                f"load_exception: {exc}",
                kind=disable_kind,
            )
            return entries

        query = self._build_query_text(statement, goal_state=goal_state)
        top = entries[:n]
        # Cache cross-encoder scores per (query, lemma) to avoid re-scoring across
        # repeated calls in the same run (goal-conditioned queries often repeat).
        scores_map: Dict[str, float] = {}
        to_score: List[Tuple[str, str]] = []
        to_score_entries: List[LemmaEntry] = []
        for e in top:
            k = self._cross_encoder_key(query, e)
            cached = self._cross_encoder_cache.get(k)
            if cached is not None:
                self._cross_encoder_cache.move_to_end(k)
                scores_map[k] = float(cached)
                continue
            to_score.append((query, f"{e.name} : {e.type}"))
            to_score_entries.append(e)

        if to_score:
            try:
                # Different prediction API for LLM vs standard CrossEncoder
                if getattr(self, "_cross_encoder_is_llm", False):
                    pairs = [[q, d] for q, d in to_score]
                    preds, layerwise_exc = self._compute_layerwise_scores_with_timeout(
                        pairs
                    )
                    if layerwise_exc is not None:
                        self._disable_layerwise_reranker(
                            f"runtime_error_or_timeout: {layerwise_exc}"
                        )
                        logger.warning(
                            "Layerwise reranker unstable (%s); auto-falling back to %s.",
                            layerwise_exc,
                            getattr(
                                self.cfg,
                                "cross_encoder_fallback_model",
                                "BAAI/bge-reranker-large",
                            ),
                        )
                        # Retry once through fallback path.
                        return self.rerank_with_cross_encoder(
                            entries,
                            statement,
                            goal_state=goal_state,
                            top_n=top_n,
                            force=True,
                        )
                    # LayerWiseFlagLLMReranker may return per-layer scores.
                    # compute_score returns scores per layer - may be numpy array or list
                    # Handle both numpy arrays and Python lists uniformly
                    if preds is not None and np is not None and hasattr(preds, "ndim"):
                        # numpy array - check if 2D (layers x samples)
                        if preds.ndim == 2:
                            preds = preds[-1]  # Use last layer's scores
                    elif isinstance(preds, (list, tuple)) and len(preds) > 0:
                        first = preds[0]
                        # Check if nested (list of lists or list of arrays)
                        if hasattr(first, "__len__") and not isinstance(
                            first, (str, bytes)
                        ):
                            preds = preds[-1]  # Use last layer's scores
                else:
                    # Standard CrossEncoder uses predict()
                    preds, ce_exc = self._predict_cross_encoder_with_timeout(to_score)
                    if ce_exc is not None:
                        if not self._cross_encoder_force_cpu_fallback:
                            self._cross_encoder_force_cpu_fallback = True
                            self._cross_encoder = None
                            logger.warning(
                                "Cross-encoder reranker unstable (%s); retrying on CPU fallback model %s.",
                                ce_exc,
                                getattr(
                                    self.cfg,
                                    "cross_encoder_fallback_model",
                                    "BAAI/bge-reranker-large",
                                ),
                            )
                            return self.rerank_with_cross_encoder(
                                entries,
                                statement,
                                goal_state=goal_state,
                                top_n=top_n,
                                force=True,
                            )
                        logger.warning(
                            "Cross-encoder rerank failed after CPU fallback (%s); skipping rerank.",
                            ce_exc,
                        )
                        disable_kind = self._classify_cross_encoder_failure(
                            ce_exc, stage="predict"
                        )
                        self._disable_cross_encoder(
                            f"predict_failed_after_cpu_fallback: {ce_exc}",
                            kind=disable_kind,
                        )
                        return entries
                if preds is None:
                    logger.warning(
                        "Cross-encoder returned None predictions; skipping rerank."
                    )
                    return entries
                for e, s in zip(to_score_entries, preds):
                    k = self._cross_encoder_key(query, e)
                    sc = float(s)
                    if not math.isfinite(sc):
                        sc = 0.0
                    scores_map[k] = sc
                    self._cache_cross_score(k, sc)
                self._mark_cross_encoder_success()
            except Exception as exc:
                logger.warning("Cross-encoder rerank failed (%s); skipping.", exc)
                disable_kind = self._classify_cross_encoder_failure(
                    exc, stage="predict"
                )
                self._disable_cross_encoder(
                    f"rerank_exception: {exc}",
                    kind=disable_kind,
                )
                return entries

        scored = [
            (e, float(scores_map.get(self._cross_encoder_key(query, e), 0.0)))
            for e in top
        ]
        scored.sort(key=lambda x: x[1], reverse=True)
        # Normalize scores to [0,1] for downstream LTR features.
        vals = [s for _, s in scored]
        if vals:
            mn = min(vals)
            mx = max(vals)
            denom = mx - mn
            if denom <= 1e-9:
                self._last_rerank_scores = {e.name: 0.5 for e, _ in scored}
            else:
                self._last_rerank_scores = {e.name: (s - mn) / denom for e, s in scored}
        return [e for e, _ in scored] + entries[n:]

    async def rerank_with_llm(
        self,
        entries: List[LemmaEntry],
        statement: str,
        *,
        goal_state: Optional[str] = None,
        client: Any = None,
        top_n: Optional[int] = None,
        force: bool = False,
        deadline: Optional[float] = None,
    ) -> List[LemmaEntry]:
        """Optional LLM reranker over top-N lemmas.

        Expects an async client with `.chat(messages, ...) -> str`.
        """
        if not entries:
            return entries
        self._last_rerank_scores = {}
        if (not force) and (self.cfg.rerank_mode or "none") != "llm":
            return entries
        if client is None:
            return entries
        n = int(top_n if top_n is not None else self.cfg.rerank_top_n)
        if n <= 0:
            return entries

        query = self._build_query_text(statement, goal_state=goal_state)
        items = entries[:n]
        lemma_lines = "\n".join(f"- {e.name} : {e.type}" for e in items)
        system = (
            STEERING_DIRECTIVE + "You are a theorem-proving lemma reranker.\n"
            "Given a goal (Lean statement + optional goal state) and candidate lemmas, "
            "assign each lemma a relevance score in [0,1].\n"
            "Output ONLY lines of the form:\n"
            "LEMMA: <name> SCORE: <float>\n"
            "Do not output commentary."
        )
        user = f"GOAL:\n{query}\n\nCANDIDATE LEMMAS:\n{lemma_lines}\n"
        chat_kwargs: Dict[str, Any] = {}
        if deadline is not None:
            chat_kwargs["deadline"] = deadline
        try:
            raw = await client.chat(
                [
                    {"role": "system", "content": system},
                    {"role": "user", "content": user},
                ],
                **chat_kwargs,
            )
            if getattr(client, "last_truncated", False):
                logger.warning("LLM rerank response truncated (max_tokens hit)")
        except Exception as exc:
            logger.warning("LLM rerank failed (%s); skipping.", exc)
            return entries

        score_map: Dict[str, float] = {}
        for line in (raw or "").splitlines():
            m = re.match(
                r"\s*LEMMA\s*:\s*([A-Za-z0-9_'.]+)\s+SCORE\s*:\s*([0-9]*\.?[0-9]+)\s*$",
                line.strip(),
                re.IGNORECASE,
            )
            if not m:
                continue
            name = m.group(1).strip()
            try:
                sc = float(m.group(2))
            except Exception as exc:
                logger.debug("LLM rerank: failed to parse score for %s: %s", name, exc)
                continue
            score_map[name] = max(0.0, min(1.0, sc))

        if not score_map:
            return entries

        # For lemmas the LLM didn't score, use a position-based fallback that
        # preserves the pre-rerank ordering instead of penalizing to 0.0.
        scored_vals = list(score_map.values())
        fallback_base = min(scored_vals) if scored_vals else 0.5

        def _sort_key(t: Tuple[int, LemmaEntry]) -> Tuple[float, float]:
            idx, e = t
            s = score_map.get(e.name, fallback_base - 1e-6)
            return (s, 1.0 - idx / max(1.0, float(n)))

        reranked_top = sorted(enumerate(items), key=_sort_key, reverse=True)
        self._last_rerank_scores = {
            e.name: float(score_map.get(e.name, fallback_base)) for e in items
        }
        return [e for _, e in reranked_top] + entries[n:]

    def format_context(self, entries: Sequence[LemmaEntry]) -> str:
        lines: List[str] = []
        for e in entries:
            if e.docstring and self.cfg.include_docstrings:
                lines.append(f"{e.name} : {e.type}  -- {e.docstring}")
            else:
                lines.append(f"{e.name} : {e.type}")
        return "\n".join(lines)
