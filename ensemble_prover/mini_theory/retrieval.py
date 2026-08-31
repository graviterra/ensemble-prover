"""Deterministic retrieval over verified, published Mini theory declarations."""

from __future__ import annotations

import math
import re
from collections import Counter
from dataclasses import dataclass
from typing import Callable, Iterable, Optional, Sequence

from .model import PublishedTheoryBundle, TheoryDeclaration
from .store import TheoryStore, TheoryStoreError


_TOKEN_RE = re.compile(r"[A-Za-z0-9_']+")
_SYMBOL_MAP = {
    "∀": "forall",
    "∃": "exists",
    "∑": "sum",
    "→": "arrow",
    "↔": "iff",
    "≤": "le",
    "≥": "ge",
    "≠": "ne",
    "∈": "mem",
    "⊆": "subset",
    "∣": "dvd",
}

# Tokens that describe Lean surface syntax rather than mathematical content.
# They may contribute to diagnostics, but must never be sufficient to admit a
# retrieval hit. In particular, the old scorer matched unrelated theorems on
# bound names plus ``Fin``/``->`` at exactly the acceptance threshold.
_GENERIC_RETRIEVAL_TOKENS = frozenset(
    {
        "a", "b", "c", "f", "g", "h", "i", "j", "k", "m", "n", "x", "y", "z",
        "arrow", "exists", "forall", "iff", "prop", "type",
        "fin", "nat", "int", "real", "set", "finset",
        "theorem", "lemma", "general", "mathematics",
    }
)


def _tokens(text: str) -> tuple[str, ...]:
    expanded = str(text or "")
    for symbol, token in _SYMBOL_MAP.items():
        expanded = expanded.replace(symbol, f" {token} ")
    expanded = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", expanded)
    raw = [
        part.lower().strip("'")
        for item in _TOKEN_RE.findall(expanded)
        for part in item.replace("_", " ").split()
    ]
    out: list[str] = []
    for token in raw:
        if token and token not in out:
            out.append(token)
    return tuple(out)


@dataclass(frozen=True)
class TheorySearchHit:
    fq_name: str
    declaration_kind: str
    type_text: str
    module_name: str
    bundle_id: str
    domain: str
    dependency_bundle_ids: tuple[str, ...]
    referenced_constants: tuple[str, ...]
    score: float
    reasons: tuple[str, ...]


class MiniTheoryRetriever:
    """Search only the store's independently verified theory manifests."""

    def __init__(self, store: TheoryStore) -> None:
        self.store = store
        self._bundles: dict[str, PublishedTheoryBundle] = {}
        self._entries: list[tuple[PublishedTheoryBundle, TheoryDeclaration]] = []
        self._document_frequency: Counter[str] = Counter()
        self.refresh()

    def refresh(self) -> None:
        self.refresh_from_bundles(self.store.iter_bundles())

    def refresh_from_bundles(
        self,
        bundles: Iterable[PublishedTheoryBundle],
    ) -> None:
        """Refresh from one already integrity-checked immutable store view."""

        bundles = list(bundles)
        self._bundles = {bundle.bundle_id: bundle for bundle in bundles}
        self._entries = [
            (bundle, declaration)
            for bundle in bundles
            if bundle.status == "published"
            for declaration in bundle.declarations
        ]
        self._document_frequency.clear()
        for bundle, declaration in self._entries:
            self._document_frequency.update(
                set(self._entry_tokens(bundle, declaration))
            )

    def search(
        self,
        query_text: str,
        *,
        goal_state: str = "",
        domain: str = "",
        declaration_kinds: Sequence[str] = (),
        eligible_bundle_ids: Optional[Sequence[str]] = None,
        max_results: int = 10,
        deadline_exhausted: Optional[Callable[[], bool]] = None,
        admission_predicate: Optional[Callable[[TheorySearchHit], bool]] = None,
    ) -> list[TheorySearchHit]:
        query_tokens = set(_tokens(f"{query_text} {goal_state}"))
        if not query_tokens or max(0, int(max_results or 0)) <= 0:
            return []
        domain_key = str(domain or "").strip().lower()
        kinds = {str(item or "").strip() for item in declaration_kinds if str(item or "").strip()}
        eligible = (
            {
                str(item or "").strip()
                for item in eligible_bundle_ids
                if str(item or "").strip()
            }
            if eligible_bundle_ids is not None
            else None
        )
        if eligible is None:
            searchable_entries = self._entries
            document_frequency = self._document_frequency
        else:
            searchable_entries = [
                (bundle, declaration)
                for bundle, declaration in self._entries
                if bundle.bundle_id in eligible
            ]
            document_frequency = Counter()
            for bundle, declaration in searchable_entries:
                document_frequency.update(
                    set(self._entry_tokens(bundle, declaration))
                )
        scored: list[TheorySearchHit] = []
        document_count = max(1, len(searchable_entries))
        for _idx, (bundle, declaration) in enumerate(searchable_entries):
            # Cooperative cancel: this scoring loop runs under the caller's
            # library_lock, so honor the retrieval deadline (checked cheaply
            # every 128 entries) instead of blocking the lock/slot past it.
            if (
                deadline_exhausted is not None
                and (_idx & 127) == 0
                and deadline_exhausted()
            ):
                break
            if domain_key and bundle.domain.strip().lower() != domain_key:
                continue
            if kinds and declaration.declaration_kind not in kinds:
                continue
            entry_tokens = set(self._entry_tokens(bundle, declaration))
            overlap = query_tokens & entry_tokens
            semantic_overlap = overlap - _GENERIC_RETRIEVAL_TOKENS
            name_tokens = set(_tokens(declaration.fq_name.rsplit(".", 1)[-1]))
            name_overlap = query_tokens & name_tokens
            exact_name = str(query_text or "").strip() in {
                declaration.fq_name,
                declaration.fq_name.rsplit(".", 1)[-1],
            }
            exact_type = " ".join(str(query_text or "").split()) == " ".join(
                str(declaration.type_text or "").split()
            )
            if not semantic_overlap and not exact_name and not exact_type:
                continue
            lexical = sum(
                math.log((document_count + 1) / (1 + document_frequency[token]))
                + 1.0
                for token in overlap
            )
            score = lexical + 2.5 * len(name_overlap) + (20.0 if exact_name else 0.0)
            reasons = []
            if exact_name:
                reasons.append("exact_name")
            if exact_type:
                reasons.append("exact_type")
            if name_overlap:
                reasons.append("name_overlap:" + ",".join(sorted(name_overlap)))
            if overlap:
                reasons.append("token_overlap:" + ",".join(sorted(overlap)))
            if semantic_overlap:
                reasons.append(
                    "semantic_overlap:" + ",".join(sorted(semantic_overlap))
                )
            hit = TheorySearchHit(
                    fq_name=declaration.fq_name,
                    declaration_kind=declaration.declaration_kind,
                    type_text=declaration.type_text,
                    module_name=bundle.module_name,
                    bundle_id=bundle.bundle_id,
                    domain=bundle.domain,
                    dependency_bundle_ids=bundle.dependency_bundle_ids,
                    referenced_constants=declaration.referenced_constants,
                    score=score,
                    reasons=tuple(reasons),
                )
            if admission_predicate is not None and not admission_predicate(hit):
                continue
            scored.append(hit)
        scored.sort(key=lambda hit: (-hit.score, hit.fq_name, hit.bundle_id))
        return scored[: max(0, int(max_results or 0))]

    def get_by_name(self, fq_name: str) -> Optional[TheorySearchHit]:
        wanted = str(fq_name or "").strip()
        for bundle, declaration in self._entries:
            if declaration.fq_name != wanted:
                continue
            return TheorySearchHit(
                fq_name=declaration.fq_name,
                declaration_kind=declaration.declaration_kind,
                type_text=declaration.type_text,
                module_name=bundle.module_name,
                bundle_id=bundle.bundle_id,
                domain=bundle.domain,
                dependency_bundle_ids=bundle.dependency_bundle_ids,
                referenced_constants=declaration.referenced_constants,
                score=float("inf"),
                reasons=("exact_name",),
            )
        return None

    def required_modules(self, bundle_ids: Iterable[str]) -> tuple[str, ...]:
        """Return dependency-first modules for an exact bundle selection."""

        ordered: list[str] = []
        visited: set[str] = set()
        active: set[str] = set()

        def visit(bundle_id: str) -> None:
            key = str(bundle_id or "").strip()
            if key in visited:
                return
            if key in active:
                raise TheoryStoreError(f"theory dependency cycle at {key}")
            bundle = self._bundles.get(key)
            if bundle is None:
                raise TheoryStoreError(f"missing theory dependency bundle {key}")
            active.add(key)
            for dependency in bundle.dependency_bundle_ids:
                visit(dependency)
            active.remove(key)
            visited.add(key)
            if bundle.module_name not in ordered:
                ordered.append(bundle.module_name)

        for bundle_id in bundle_ids:
            visit(str(bundle_id or ""))
        return tuple(ordered)

    @staticmethod
    def _entry_tokens(
        bundle: PublishedTheoryBundle,
        declaration: TheoryDeclaration,
    ) -> tuple[str, ...]:
        return _tokens(
            " ".join(
                (
                    declaration.fq_name,
                    declaration.declaration_kind,
                    declaration.type_text,
                    declaration.docstring,
                    " ".join(declaration.referenced_constants),
                    bundle.domain,
                )
            )
        )
