"""Deterministic and model-backed text embeddings used by retrieval."""

from __future__ import annotations

import logging
import os
import re
import socket
import threading
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import List, Optional, Protocol

from .math_utils import l2_normalize

logger = logging.getLogger(__name__)

_ENV_LOCK = threading.Lock()
_EMBED_INIT_WORKER_SLOTS = threading.BoundedSemaphore(2)
_DNS_WORKER_SLOTS = threading.BoundedSemaphore(2)


class TextEmbedder(Protocol):
    dim: int

    def embed(self, text: str) -> List[float]: ...

    def embed_many(self, texts: List[str]) -> List[List[float]]:
        """Embed multiple texts.  Default implementation calls embed per-text."""
        return [self.embed(t) for t in texts]


def _hashed_embedding_tokens(text: str) -> List[str]:
    """Return the stable identifier tokens used by the hashed embedder."""
    return re.findall(r"[A-Za-z_][A-Za-z0-9_']*", text)


def _hash_embedding_token(token: str, seed: int) -> int:
    """Return the legacy deterministic FNV-1a-style token hash."""
    value = 2166136261
    for char in token:
        value ^= ord(char)
        value *= 16777619
        value &= 0xFFFFFFFF
    return value ^ (seed & 0xFFFFFFFF)


class HashedEmbedder:
    """Dependency-free deterministic text embedder.

    This compatibility backend belongs to the neutral embedding layer; it has
    no dependency on the retired V1 ensemble controller.
    """

    def __init__(self, dim: int = 256, seed: int = 1337):
        self.dim = dim
        self.seed = seed

    def embed(self, text: str) -> List[float]:
        vector = [0.0] * self.dim
        for token in _hashed_embedding_tokens(text):
            token_hash = _hash_embedding_token(token, self.seed)
            index = token_hash % self.dim
            sign = 1.0 if (token_hash >> 8) & 1 else -1.0
            vector[index] += sign
        return l2_normalize(vector)

    def embed_many(self, texts: List[str]) -> List[List[float]]:
        return [self.embed(text) for text in texts]


@dataclass
class EmbedderConfig:
    backend: str = "sentence_transformers"  # "hashed" | "sentence_transformers"
    model: str = "BAAI/bge-base-en-v1.5"
    device: Optional[str] = None
    normalize: bool = True
    # sentence-transformers load policy
    prefer_local_files: bool = True
    local_files_only: bool = True
    allow_download: bool = False
    init_timeout_s: float = 8.0
    dim: int = 768
    seed: int = 1337


def _run_with_timeout(fn, *, timeout_s: float, label: str):
    slots = _EMBED_INIT_WORKER_SLOTS
    if not slots.acquire(blocking=False):
        raise RuntimeError("embedding initialization worker capacity exhausted")
    timeout = max(1.0, float(timeout_s))
    done = threading.Event()
    box: dict[str, object] = {"value": None, "exc": None}

    def _worker() -> None:
        try:
            box["value"] = fn()
        except BaseException as exc:
            box["exc"] = exc
        finally:
            slots.release()
            done.set()

    t = threading.Thread(target=_worker, name=f"{label}-worker", daemon=True)
    try:
        t.start()
    except BaseException:
        slots.release()
        raise
    if not done.wait(timeout=timeout):
        raise TimeoutError(f"{label} exceeded timeout ({timeout:.1f}s)")
    if box["exc"] is not None:
        raise box["exc"]  # type: ignore[misc]
    return box["value"]


def _can_resolve_host(host: str, timeout_s: float = 1.5) -> bool:
    slots = _DNS_WORKER_SLOTS
    if not slots.acquire(blocking=False):
        return False
    done = threading.Event()
    ok = {"value": False}

    def _worker() -> None:
        try:
            socket.getaddrinfo(host, 443)
            ok["value"] = True
        except Exception:
            ok["value"] = False
        finally:
            slots.release()
            done.set()

    t = threading.Thread(target=_worker, name="hf-dns-probe", daemon=True)
    try:
        t.start()
    except BaseException:
        slots.release()
        raise
    if not done.wait(timeout=max(0.2, float(timeout_s))):
        return False
    return bool(ok["value"])


def _set_hf_hub_timeouts() -> None:
    # Keep hub network waits bounded when downloads are allowed.
    os.environ.setdefault("HF_HUB_ETAG_TIMEOUT", "4")
    os.environ.setdefault("HF_HUB_DOWNLOAD_TIMEOUT", "8")


class SentenceTransformerEmbedder:
    def __init__(
        self,
        model_name: str,
        device: Optional[str] = None,
        normalize: bool = True,
        *,
        prefer_local_files: bool = True,
        local_files_only: bool = False,
        allow_download: bool = True,
        init_timeout_s: float = 20.0,
    ):
        try:
            from sentence_transformers import SentenceTransformer  # type: ignore
        except Exception as exc:  # pragma: no cover - optional dependency
            raise ImportError(
                "sentence-transformers is required for semantic embeddings. "
                "Install with: pip install sentence-transformers"
            ) from exc

        _set_hf_hub_timeouts()

        def _load(local_only: bool):
            kwargs: dict[str, object] = {}
            if device is not None:
                kwargs["device"] = device
            kwargs["local_files_only"] = bool(local_only)
            try:
                return SentenceTransformer(model_name, **kwargs)  # type: ignore[arg-type]
            except TypeError:
                # Back-compat for older ST versions without local_files_only kwarg.
                kwargs.pop("local_files_only", None)
                return SentenceTransformer(model_name, **kwargs)  # type: ignore[arg-type]

        timeout_s = max(1.0, float(init_timeout_s))
        is_local_path = Path(model_name).exists()
        want_local_first = bool(
            local_files_only
            or prefer_local_files
            or is_local_path
            or not allow_download
        )
        local_exc: Optional[BaseException] = None

        model = None
        if want_local_first:
            # Env-var manipulation happens in the calling thread so the
            # finally block runs even when _run_with_timeout times out,
            # preventing _ENV_LOCK from being held indefinitely.
            _ENV_LOCK.acquire()
            prev_hf = os.environ.get("HF_HUB_OFFLINE")
            prev_tx = os.environ.get("TRANSFORMERS_OFFLINE")
            os.environ["HF_HUB_OFFLINE"] = "1"
            os.environ["TRANSFORMERS_OFFLINE"] = "1"
            try:
                model = _run_with_timeout(
                    lambda: _load(True),
                    timeout_s=timeout_s,
                    label="sentence-transformers local load",
                )
            except BaseException as exc:
                local_exc = exc
                if local_files_only or is_local_path or not allow_download:
                    raise RuntimeError(
                        f"sentence-transformers local-only load failed for '{model_name}' "
                        f"(downloads disabled): {exc}"
                    ) from exc
            finally:
                if prev_hf is None:
                    os.environ.pop("HF_HUB_OFFLINE", None)
                else:
                    os.environ["HF_HUB_OFFLINE"] = prev_hf
                if prev_tx is None:
                    os.environ.pop("TRANSFORMERS_OFFLINE", None)
                else:
                    os.environ["TRANSFORMERS_OFFLINE"] = prev_tx
                _ENV_LOCK.release()

        if model is None:
            if not is_local_path and not _can_resolve_host(
                "huggingface.co", timeout_s=min(2.0, timeout_s / 2.0)
            ):
                raise RuntimeError(
                    f"Cannot resolve huggingface.co while loading '{model_name}'. "
                    "Use local cache or hashed embeddings."
                ) from local_exc
            model = _run_with_timeout(
                lambda: _load(False),
                timeout_s=timeout_s,
                label="sentence-transformers network load",
            )

        self.model = model
        self.normalize = normalize
        self.dim = int(self.model.get_sentence_embedding_dimension())

    def embed(self, text: str) -> List[float]:
        # sentence-transformers handles tokenization + batching internally
        emb = self.model.encode(text, normalize_embeddings=self.normalize)
        return emb.tolist() if hasattr(emb, "tolist") else list(emb)

    def embed_many(self, texts: List[str]) -> List[List[float]]:
        """Embed many texts in a single batch (significantly faster for ST)."""
        if not texts:
            return []
        embs = self.model.encode(texts, normalize_embeddings=self.normalize)
        # numpy array / torch tensor both support .tolist()
        if hasattr(embs, "tolist"):
            return embs.tolist()
        # Fallback: best-effort conversion
        return [list(v) for v in embs]  # type: ignore[iteration-over-annotated-type]


@lru_cache(maxsize=16)
def _cached_sentence_transformer_embedder(
    model: str,
    device: Optional[str],
    normalize: bool,
    prefer_local_files: bool,
    local_files_only: bool,
    allow_download: bool,
    init_timeout_s: float,
) -> SentenceTransformerEmbedder:
    return SentenceTransformerEmbedder(
        model,
        device=device,
        normalize=normalize,
        prefer_local_files=prefer_local_files,
        local_files_only=local_files_only,
        allow_download=allow_download,
        init_timeout_s=init_timeout_s,
    )


@lru_cache(maxsize=1)
def get_default_embedder() -> TextEmbedder:
    return make_embedder(EmbedderConfig())


def make_embedder(cfg: EmbedderConfig) -> TextEmbedder:
    backend = (cfg.backend or "sentence_transformers").lower().strip()
    if backend == "sentence_transformers":
        logger.info("Using sentence-transformers embedder: %s", cfg.model)
        return _cached_sentence_transformer_embedder(
            cfg.model,
            device=cfg.device,
            normalize=cfg.normalize,
            prefer_local_files=bool(cfg.prefer_local_files),
            local_files_only=bool(cfg.local_files_only),
            allow_download=bool(cfg.allow_download),
            init_timeout_s=float(cfg.init_timeout_s),
        )
    if backend == "hashed":
        return HashedEmbedder(dim=cfg.dim, seed=cfg.seed)
    raise ValueError(
        f"Unknown embedder backend '{cfg.backend}'. "
        "Supported backends: 'sentence_transformers', 'hashed'."
    )
