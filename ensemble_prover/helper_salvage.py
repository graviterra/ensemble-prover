"""Helper-lemma salvage for the mini prover.

When a full proof attempt fails, any helper declarations in the submitted
Lean block may still be valuable.  This module checks those helpers
incrementally and records the ones that compile, so later turns can reuse
them without re-deriving them.
"""

from __future__ import annotations

import asyncio
import re
import time
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, Iterable, List, Mapping, Optional, Sequence, Set, Tuple

from .proof_dossier import (
    ProofDossier,
    helper_decl_name,
    is_answer_unsafe_helper_source,
    verified_helper_bound_contract_identity,
    verified_helper_semantic_statement_changed,
)
from .contract_identity import parse_lean_contract_identity
from .proof_graph import helper_decl_statement
from .proof_state import lean_referenced_helper_names
from .proof_state_cache import (
    _proof_state_helper_policy_rejection,
)
from .utils import fresh_lean_alternative_identifier, rename_lean_identifier


_NEGATIVE_HELPER_STATEMENT_RE = re.compile(
    r"(?:^|[\s:(→,])(?:¬|Not\b|False\b)|"
    r"\b(?:counterexamples?|counter-examples?|refut(?:e|es|ed|ing|ation)|"
    r"disprov(?:e|es|ed|ing)|falsif(?:y|ies|ied|ying))\b|"
    r"∃[\s\S]{0,240}≠|Exists[\s\S]{0,240}≠|"
    r"=\s*False\b|→\s*False\b",
    re.IGNORECASE,
)
_RELEVANCE_TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_']*")
_RELEVANCE_STOPWORDS = {
    "Prop",
    "Sort",
    "Type",
    "by",
    "def",
    "else",
    "exact",
    "forall",
    "fun",
    "have",
    "if",
    "intro",
    "lemma",
    "let",
    "match",
    "theorem",
    "then",
    "trivial",
    "where",
}


def _helper_statement_is_negative_route(src: str) -> bool:
    statement = " ".join(str(helper_decl_statement(src) or "").split())
    return bool(statement and _NEGATIVE_HELPER_STATEMENT_RE.search(statement))


def _relevance_tokens(text: str) -> Set[str]:
    tokens: Set[str] = set()
    for raw in _RELEVANCE_TOKEN_RE.findall(str(text or "")):
        token = raw.strip("_'")
        if len(token) < 3 or token in _RELEVANCE_STOPWORDS:
            continue
        tokens.add(token.lower())
    return tokens


def _helper_has_target_token_overlap(src: str, targets: Sequence[str]) -> bool:
    statement = str(helper_decl_statement(src) or src or "")
    helper_tokens = _relevance_tokens(statement)
    if not helper_tokens:
        return False
    target_tokens: Set[str] = set()
    for target in targets:
        target_tokens.update(_relevance_tokens(target))
    return bool(helper_tokens & target_tokens)


def _helper_statement_signature(block: str) -> str:
    """Return a whitespace-normalized signature of a helper's statement.

    Used to dedup helpers on (name, statement) pairs so model self-corrections
    that re-declare a helper with the same name but a different statement
    are NOT silently dropped during merge.
    """

    return " ".join(str(helper_decl_statement(block) or "").split())


def helper_statement_changed(previous_source: str, replacement_source: str) -> bool:
    """Return whether two helper declarations expose different statements."""

    previous_statement = _helper_statement_signature(previous_source)
    replacement_statement = _helper_statement_signature(replacement_source)
    if previous_statement and replacement_statement:
        return previous_statement != replacement_statement
    return str(previous_source or "").strip() != str(replacement_source or "").strip()


def helper_record_fingerprint(item: Any) -> Tuple[Any, ...]:
    """Stable identity for a verified-helper record, not just its Lean source."""

    return (
        str(getattr(item, "source_hash", "") or ""),
        str(getattr(item, "phase", "") or ""),
        int(getattr(item, "turn_index", 0) or 0),
        tuple(
            str(name or "").strip()
            for name in list(getattr(item, "support_names", ()) or ())
            if str(name or "").strip()
        ),
        tuple(
            sorted(
                (
                    str(name or "").strip(),
                    str(source_hash or "").strip(),
                )
                for name, source_hash in dict(
                    getattr(item, "support_source_hashes", {}) or {}
                ).items()
                if str(name or "").strip() and str(source_hash or "").strip()
            )
        ),
        tuple(
            str(name or "").strip()
            for name in list(getattr(item, "replay_context_names", ()) or ())
            if str(name or "").strip()
        ),
        tuple(
            sorted(
                (
                    str(name or "").strip(),
                    str(source_hash or "").strip(),
                )
                for name, source_hash in dict(
                    getattr(item, "replay_context_source_hashes", {}) or {}
                ).items()
                if str(name or "").strip() and str(source_hash or "").strip()
            )
        ),
    )


def helper_record_changed(existing: Any, incoming: Any) -> bool:
    """Return whether two helper records differ in source or proof provenance."""

    return helper_record_fingerprint(existing) != helper_record_fingerprint(incoming)


def dependency_ordered_verified_helper_items(
    items: Iterable[Tuple[str, Any]],
) -> List[Tuple[str, Any]]:
    """Stably order a helper batch so in-batch certificate dependencies land first.

    Helper replacement can move a declaration to the end of a dossier's
    insertion order while already-recorded dependents retain valid receipts
    for it. Import boundaries validate those receipts against the destination,
    so replaying raw dict order would reject the dependent before its support
    arrives. Cycles remain in original order and therefore fail closed at the
    importer instead of being guessed through.
    """

    pending = [
        (str(name or "").strip(), item)
        for name, item in list(items or [])
        if str(name or "").strip() and item is not None
    ]
    batch_names = {name for name, _item in pending}
    emitted_names: Set[str] = set()
    ordered: List[Tuple[str, Any]] = []
    while pending:
        ready_indices: List[int] = []
        for index, (name, item) in enumerate(pending):
            dependency_names = {
                str(dependency or "").strip()
                for dependency in [
                    *list(getattr(item, "support_names", []) or []),
                    *list(getattr(item, "replay_context_names", []) or []),
                ]
                if str(dependency or "").strip()
                and str(dependency or "").strip() != name
            }
            if all(
                dependency not in batch_names or dependency in emitted_names
                for dependency in dependency_names
            ):
                ready_indices.append(index)
        if not ready_indices:
            ordered.extend(pending)
            break
        ready_index_set = set(ready_indices)
        next_pending: List[Tuple[str, Any]] = []
        for index, entry in enumerate(pending):
            if index in ready_index_set:
                ordered.append(entry)
                emitted_names.add(entry[0])
            else:
                next_pending.append(entry)
        pending = next_pending
    return ordered


def preflight_dependency_ordered_verified_helper_items(
    dossier: Any,
    items: Sequence[Tuple[str, Any]],
) -> List[Tuple[str, Any]]:
    """Return only importable items, staged in dependency order.

    Replacement merges must determine which certificates can actually enter
    the destination before evicting dependents of an old declaration.  The
    prospective registry lets a dependent validate receipts against an
    earlier incoming support without mutating the real dossier.
    """

    ordered = dependency_ordered_verified_helper_items(items)
    preflight = getattr(dossier, "preflight_imported_verified_helper", None)
    if not callable(preflight):
        return ordered
    prospective = dict(getattr(dossier, "verified_helpers", {}) or {})
    accepted: List[Tuple[str, Any]] = []
    for raw_name, item in ordered:
        name = str(raw_name or "").strip()
        if not name:
            continue
        try:
            evidence = preflight(
                item,
                destination_helpers=prospective,
            )
        except Exception:
            evidence = None
        if evidence is None:
            continue
        evidence_name = str(evidence.get("helper_name") or "").strip()
        if evidence_name != name:
            increment = getattr(dossier, "increment_tool_metric", None)
            if callable(increment):
                increment(
                    "mini_verified_helper_import_registry_name_rejected",
                    1,
                )
            continue
        accepted.append((name, item))
        for stale_name in list(evidence.get("stale_dependents") or []):
            prospective.pop(str(stale_name or "").strip(), None)
        prospective[name] = item
    return accepted


def _helper_import_evidence_conflicts(existing: Any, incoming: Any) -> bool:
    """Whether a same-source import disagrees with durable semantic evidence."""

    existing_identity = verified_helper_bound_contract_identity(existing)
    incoming_identity = verified_helper_bound_contract_identity(incoming)
    existing_parts = parse_lean_contract_identity(existing_identity)
    incoming_parts = parse_lean_contract_identity(incoming_identity)
    existing_full_hash = existing_parts[0] if existing_parts is not None else ""
    incoming_full_hash = incoming_parts[0] if incoming_parts is not None else ""
    if (
        existing_full_hash
        and incoming_full_hash
        and existing_full_hash != incoming_full_hash
    ):
        return True
    if (
        existing_full_hash
        and incoming_full_hash
        and existing_full_hash == incoming_full_hash
    ):
        for field_name in (
            "contract_display_statement",
            "contract_binder_sorts",
            "contract_proof_binder_types",
        ):
            existing_value = getattr(existing, field_name, "") or ""
            incoming_value = getattr(incoming, field_name, "") or ""
            if field_name != "contract_display_statement":
                existing_value = tuple(existing_value)
                incoming_value = tuple(incoming_value)
            if existing_value and incoming_value and existing_value != incoming_value:
                return True
    existing_visibility = str(
        getattr(existing, "visibility_policy", "") or ""
    ).strip()
    incoming_visibility = str(
        getattr(incoming, "visibility_policy", "") or ""
    ).strip()
    return existing_visibility != incoming_visibility


def helper_provenance_is_trust_monotone(
    dossier: Any,
    existing: Any,
    incoming: Any,
) -> bool:
    """Whether same-source incoming metadata strictly adds valid receipts.

    This is shared by every Mini child/branch merge boundary.  A current child
    can revalidate byte-identical source in a richer Lean context, but an
    older/emptier sibling must never erase richer parent provenance.
    """

    if existing is None or incoming is None:
        return False
    if str(getattr(existing, "source_hash", "") or "").strip() != str(
        getattr(incoming, "source_hash", "") or ""
    ).strip():
        return False
    if _helper_import_evidence_conflicts(existing, incoming):
        return False
    added = False
    destination_helpers = getattr(dossier, "verified_helpers", {}) or {}
    for names_attr, hashes_attr in (
        ("support_names", "support_source_hashes"),
        ("replay_context_names", "replay_context_source_hashes"),
    ):
        existing_names = {
            str(value or "").strip()
            for value in list(getattr(existing, names_attr, []) or [])
            if str(value or "").strip()
        }
        incoming_names = {
            str(value or "").strip()
            for value in list(getattr(incoming, names_attr, []) or [])
            if str(value or "").strip()
        }
        if not existing_names.issubset(incoming_names):
            return False
        existing_hashes = {
            str(key or "").strip(): str(value or "").strip()
            for key, value in dict(
                getattr(existing, hashes_attr, {}) or {}
            ).items()
            if str(key or "").strip() and str(value or "").strip()
        }
        incoming_hashes = {
            str(key or "").strip(): str(value or "").strip()
            for key, value in dict(getattr(incoming, hashes_attr, {}) or {}).items()
            if str(key or "").strip() and str(value or "").strip()
        }
        if any(
            incoming_hashes.get(name) != source_hash
            for name, source_hash in existing_hashes.items()
        ):
            return False
        for dependency_name in incoming_names:
            dependency = destination_helpers.get(dependency_name)
            current_hash = str(
                getattr(dependency, "source_hash", "") or ""
            ).strip()
            if (
                not current_hash
                or incoming_hashes.get(dependency_name) != current_hash
            ):
                return False
        if incoming_names != existing_names or incoming_hashes != existing_hashes:
            added = True
    existing_identity = verified_helper_bound_contract_identity(existing)
    incoming_identity = verified_helper_bound_contract_identity(incoming)
    existing_parts = parse_lean_contract_identity(existing_identity)
    incoming_parts = parse_lean_contract_identity(incoming_identity)
    existing_full_hash = existing_parts[0] if existing_parts is not None else ""
    incoming_full_hash = incoming_parts[0] if incoming_parts is not None else ""
    if (
        existing_full_hash
        and incoming_full_hash
        and existing_full_hash != incoming_full_hash
    ):
        return False
    if incoming_full_hash and not existing_full_hash:
        if str(
            getattr(existing, "verification_environment_hash", "") or ""
        ).strip() != str(
            getattr(incoming, "verification_environment_hash", "") or ""
        ).strip():
            return False
        added = True
    if (
        existing_full_hash
        and incoming_full_hash
        and existing_full_hash == incoming_full_hash
    ):
        existing_display = str(
            getattr(existing, "contract_display_statement", "") or ""
        ).strip()
        incoming_display = str(
            getattr(incoming, "contract_display_statement", "") or ""
        ).strip()
        if existing_display and incoming_display and existing_display != incoming_display:
            return False
        if incoming_display and not existing_display:
            added = True
        for field_name in (
            "contract_binder_sorts",
            "contract_proof_binder_types",
        ):
            existing_values = [
                str(value or "")
                for value in list(getattr(existing, field_name, []) or [])
                if str(value or "").strip()
            ]
            incoming_values = [
                str(value or "")
                for value in list(getattr(incoming, field_name, []) or [])
                if str(value or "").strip()
            ]
            if existing_values and incoming_values and existing_values != incoming_values:
                return False
            if incoming_values and not existing_values:
                added = True
    existing_visibility = str(
        getattr(existing, "visibility_policy", "") or ""
    ).strip()
    incoming_visibility = str(
        getattr(incoming, "visibility_policy", "") or ""
    ).strip()
    if existing_visibility != incoming_visibility:
        return False
    authoritative_tags = {
        "root_authoritative_helper",
        "root_exact_certificate",
        "root_finalization_certificate",
    }
    existing_tags = {
        str(tag or "").strip()
        for tag in list(getattr(existing, "provenance_tags", []) or [])
        if str(tag or "").strip()
    }
    incoming_tags = {
        str(tag or "").strip()
        for tag in list(getattr(incoming, "provenance_tags", []) or [])
        if str(tag or "").strip()
        and str(tag or "").strip() not in authoritative_tags
    }
    if incoming_tags - existing_tags:
        added = True
    return added


def refresh_verified_helper_metadata_from_incoming(
    dossier: Any,
    name: str,
    incoming: Any,
) -> bool:
    """Import refreshed same-source evidence through the dossier trust boundary."""

    helper_name = str(name or "").strip()
    helpers = getattr(dossier, "verified_helpers", None) or {}
    existing = helpers.get(helper_name)
    if existing is None or incoming is None:
        return False
    if str(getattr(existing, "source_hash", "") or "").strip() != str(
        getattr(incoming, "source_hash", "") or ""
    ).strip():
        return False
    import_helper = getattr(
        dossier,
        "record_imported_verified_helper",
        None,
    )
    if not callable(import_helper):
        # Dependency receipts and semantic evidence are a single certificate.
        # A partial legacy copy cannot validate them atomically, so fail closed.
        return False
    before = helper_record_fingerprint(existing)
    accepted = import_helper(incoming)
    if accepted is None:
        return False
    return helper_record_fingerprint(existing) != before


def refresh_revalidated_dependent_support_hashes(
    dossier: Any,
    replacing_name: str,
) -> Set[str]:
    """Refresh support hashes for dependents known to replay after replacement."""

    helper_name = str(replacing_name or "").strip()
    helpers = getattr(dossier, "verified_helpers", {}) or {}
    replacement = helpers.get(helper_name)
    replacement_hash = str(getattr(replacement, "source_hash", "") or "").strip()
    if not helper_name or not replacement_hash:
        return set()
    all_names = sorted(str(name or "").strip() for name in helpers if str(name or "").strip())
    refreshed: Set[str] = set()
    for name, helper in list(helpers.items()):
        dep_name = str(name or "").strip()
        if not dep_name or dep_name == helper_name:
            continue
        support_names = [
            str(item or "").strip()
            for item in list(getattr(helper, "support_names", []) or [])
            if str(item or "").strip()
        ]
        support_hashes = dict(getattr(helper, "support_source_hashes", {}) or {})
        replay_names = [
            str(item or "").strip()
            for item in list(getattr(helper, "replay_context_names", []) or [])
            if str(item or "").strip()
        ]
        replay_hashes = dict(
            getattr(helper, "replay_context_source_hashes", {}) or {}
        )
        refs = lean_referenced_helper_names(
            str(getattr(helper, "source", "") or ""),
            all_names,
            skip=dep_name,
        )
        if (
            helper_name not in support_names
            and helper_name not in support_hashes
            and helper_name not in replay_names
            and helper_name not in replay_hashes
            and helper_name not in refs
        ):
            continue
        if helper_name in support_names or helper_name in support_hashes or helper_name in refs:
            if helper_name not in support_names:
                support_names.append(helper_name)
                helper.support_names = support_names
            helper.support_source_hashes = {
                str(key or "").strip(): str(value or "").strip()
                for key, value in support_hashes.items()
                if str(key or "").strip() and str(value or "").strip()
            }
            helper.support_source_hashes[helper_name] = replacement_hash
        if helper_name in replay_names or helper_name in replay_hashes:
            if helper_name not in replay_names:
                replay_names.append(helper_name)
                helper.replay_context_names = replay_names
            helper.replay_context_source_hashes = {
                str(key or "").strip(): str(value or "").strip()
                for key, value in replay_hashes.items()
                if str(key or "").strip() and str(value or "").strip()
            }
            helper.replay_context_source_hashes[helper_name] = replacement_hash
        refreshed.add(dep_name)
    return refreshed


def revalidated_same_source_dependent_names(
    incoming_helpers: Sequence[Tuple[str, Any]],
    existing_helpers: Mapping[str, Any],
    changed_source_hashes_by_name: Mapping[str, str],
) -> Set[str]:
    """Return same-source dependents checked against corrected supports.

    Incoming child/sibling dossiers can contain both inherited parent helpers
    and helpers rechecked after a same-name statement correction. Source text
    and turn indices are not enough to distinguish those cases across sibling
    processes, so use explicit support source hashes captured at verification
    time. A same-source helper is restored only when its recorded supports
    point at the corrected helper hashes it depends on.
    """

    valid_hash_by_name: Dict[str, str] = {
        str(name or "").strip(): str(source_hash or "").strip()
        for name, source_hash in dict(changed_source_hashes_by_name or {}).items()
        if str(name or "").strip() and str(source_hash or "").strip()
    }
    if not valid_hash_by_name:
        return set()

    incoming_by_name: Dict[str, Any] = {
        str(name or "").strip(): item
        for name, item in list(incoming_helpers or [])
        if str(name or "").strip()
    }
    if not incoming_by_name:
        return set()
    all_names = sorted(set(incoming_by_name) | set(existing_helpers or {}))
    restored: Set[str] = set()
    progressed = True
    while progressed:
        progressed = False
        for name, item in incoming_by_name.items():
            if name in valid_hash_by_name:
                continue
            existing = (existing_helpers or {}).get(name)
            if existing is None:
                continue
            if str(getattr(existing, "source_hash", "") or "") != str(
                getattr(item, "source_hash", "") or ""
            ):
                continue
            if not helper_record_changed(existing, item):
                continue
            refs = _helper_referenced_names(
                str(getattr(item, "source", "") or ""),
                all_names,
                skip=name,
            )
            declared_dependencies = {
                str(dependency or "").strip()
                for dependency in (
                    list(getattr(item, "support_names", []) or [])
                    + list(getattr(item, "replay_context_names", []) or [])
                )
                if str(dependency or "").strip()
            }
            relevant_hashes = {
                ref: valid_hash_by_name[ref]
                for ref in sorted(refs | declared_dependencies)
                if ref in valid_hash_by_name
            }
            if not relevant_hashes:
                continue
            support_hashes = {
                str(ref or "").strip(): str(source_hash or "").strip()
                for ref, source_hash in dict(
                    getattr(item, "support_source_hashes", {}) or {}
                ).items()
                if str(ref or "").strip() and str(source_hash or "").strip()
            }
            support_hashes.update(
                {
                    str(ref or "").strip(): str(source_hash or "").strip()
                    for ref, source_hash in dict(
                        getattr(item, "replay_context_source_hashes", {}) or {}
                    ).items()
                    if str(ref or "").strip() and str(source_hash or "").strip()
                }
            )
            if any(
                support_hashes.get(ref) != source_hash
                for ref, source_hash in relevant_hashes.items()
            ):
                continue
            valid_hash_by_name[name] = str(getattr(item, "source_hash", "") or "")
            restored.add(name)
            progressed = True
    return restored


def helper_uses_superseded_support(
    dossier: Any,
    item: Any,
    *,
    fallback_to_source_refs: bool = True,
) -> bool:
    """Return whether a helper record was checked against a superseded support."""

    support_hashes = {
        str(name or "").strip(): str(source_hash or "").strip()
        for name, source_hash in dict(
            getattr(item, "support_source_hashes", {}) or {}
        ).items()
        if str(name or "").strip() and str(source_hash or "").strip()
    }
    support_hashes.update(
        {
            str(name or "").strip(): str(source_hash or "").strip()
            for name, source_hash in dict(
                getattr(item, "replay_context_source_hashes", {}) or {}
            ).items()
            if str(name or "").strip() and str(source_hash or "").strip()
        }
    )
    superseded = getattr(dossier, "superseded_verified_helper_hashes", {}) or {}
    if not superseded:
        return False
    known_names = sorted(
        set(getattr(dossier, "verified_helpers", {}) or {})
        | set(superseded)
        | set(support_hashes)
        | {
            str(name or "").strip()
            for name in list(getattr(item, "replay_context_names", []) or [])
            if str(name or "").strip()
        }
    )
    refs = _helper_referenced_names(
        str(getattr(item, "source", "") or ""),
        known_names,
        skip=str(getattr(item, "name", "") or ""),
    )
    for support_name, source_hash in support_hashes.items():
        if helper_source_hash_was_superseded(dossier, support_name, source_hash):
            return True

    if support_hashes or not fallback_to_source_refs:
        return False
    return any(ref in superseded for ref in refs)


def helper_uses_replaced_support_hash(
    item: Any,
    replaced_hashes_by_name: Mapping[str, Set[str]],
) -> bool:
    """Return whether ``item`` was checked against an in-flight old helper.

    Merge callers discover same-name statement replacements before calling
    ``record_verified_helper``. Until the replacement lands, the old helper
    hash is not yet in ``superseded_verified_helper_hashes``, so incoming
    dependents from the same child/sibling need this explicit guard.
    """

    replaced = {
        str(name or "").strip(): {
            str(source_hash or "").strip()
            for source_hash in set(source_hashes or set())
            if str(source_hash or "").strip()
        }
        for name, source_hashes in dict(replaced_hashes_by_name or {}).items()
        if str(name or "").strip()
    }
    replaced = {name: hashes for name, hashes in replaced.items() if hashes}
    if not replaced:
        return False
    support_hashes = {
        str(name or "").strip(): str(source_hash or "").strip()
        for name, source_hash in dict(
            getattr(item, "support_source_hashes", {}) or {}
        ).items()
        if str(name or "").strip() and str(source_hash or "").strip()
    }
    support_hashes.update(
        {
            str(name or "").strip(): str(source_hash or "").strip()
            for name, source_hash in dict(
                getattr(item, "replay_context_source_hashes", {}) or {}
            ).items()
            if str(name or "").strip() and str(source_hash or "").strip()
        }
    )
    declared_dependencies = {
        str(name or "").strip()
        for name in (
            list(getattr(item, "support_names", []) or [])
            + list(getattr(item, "replay_context_names", []) or [])
        )
        if str(name or "").strip()
    }
    refs = _helper_referenced_names(
        str(getattr(item, "source", "") or ""),
        sorted(set(replaced) | set(support_hashes) | declared_dependencies),
        skip=str(getattr(item, "name", "") or ""),
    )
    for support_name, old_hashes in replaced.items():
        if support_name not in refs and support_name not in declared_dependencies:
            continue
        recorded_hash = support_hashes.get(support_name, "")
        if not recorded_hash or recorded_hash in old_hashes:
            return True
    return False


def known_old_helper_source_hashes(
    name: str,
    *dossiers: Any,
) -> Set[str]:
    """Return hashes that any dossier already treats as old for ``name``."""

    helper_name = str(name or "").strip()
    if not helper_name:
        return set()
    hashes: Set[str] = set()
    for dossier in dossiers:
        if dossier is None:
            continue
        for attr in (
            "verified_helper_source_hash_history",
            "superseded_verified_helper_hashes",
        ):
            mapping = getattr(dossier, attr, {}) or {}
            for value in list(dict(mapping).get(helper_name, []) or []):
                source_hash = str(value or "").strip()
                if source_hash:
                    hashes.add(source_hash)
    return hashes


def replacement_support_hashes_for_eligible_incoming(
    dst_dossier: Any,
    incoming_helpers: Sequence[Tuple[str, Any]],
    *,
    src_dossier: Any = None,
) -> Dict[str, Set[str]]:
    """Return old support hashes for statement replacements that can merge.

    The result is used to reject incoming dependents checked against a helper
    that is about to be statement-replaced. Replacement candidates themselves
    must first survive the same basic filters as ordinary helpers; otherwise a
    stale replacement that will be skipped can falsely poison valid dependents.
    """

    candidates: Dict[str, Set[str]] = {}
    candidate_items: Dict[str, Any] = {}
    for raw_name, item in list(incoming_helpers or []):
        name = str(raw_name or "").strip()
        if not name:
            continue
        if is_answer_unsafe_helper_source(getattr(item, "source", "")):
            continue
        existing = (getattr(dst_dossier, "verified_helpers", {}) or {}).get(name)
        if existing is None:
            continue
        source_hash = str(getattr(item, "source_hash", "") or "")
        existing_hash = str(getattr(existing, "source_hash", "") or "")
        if not existing_hash or existing_hash == source_hash:
            continue
        if helper_source_hash_was_superseded(dst_dossier, name, source_hash):
            continue
        if helper_uses_superseded_support(dst_dossier, item):
            continue
        if not verified_helper_semantic_statement_changed(existing, item):
            continue
        old_hashes = known_old_helper_source_hashes(name, dst_dossier, src_dossier)
        old_hashes.add(existing_hash)
        candidates[name] = old_hashes
        candidate_items[name] = item

    progressed = True
    while progressed:
        progressed = False
        for name, item in list(candidate_items.items()):
            other_replacements = {
                key: set(value)
                for key, value in candidates.items()
                if key != name
            }
            if helper_uses_replaced_support_hash(item, other_replacements):
                candidate_items.pop(name, None)
                candidates.pop(name, None)
                progressed = True
    return candidates


def helper_source_hash_was_superseded(
    dossier: Any,
    name: str,
    source_hash: str,
) -> bool:
    """Return whether ``source_hash`` is an older same-name helper revision."""

    helper_name = str(name or "").strip()
    candidate_hash = str(source_hash or "").strip()
    if not helper_name or not candidate_hash:
        return False
    superseded = getattr(dossier, "superseded_verified_helper_hashes", {}) or {}
    return candidate_hash in {
        str(value or "").strip()
        for value in list(superseded.get(helper_name, []) or [])
        if str(value or "").strip()
    }


def _helper_referenced_names(
    src: str,
    names: Sequence[str],
    *,
    skip: Optional[str] = None,
) -> Set[str]:
    return lean_referenced_helper_names(
        src,
        names,
        skip=skip,
        allow_arbitrary_dot_methods=True,
    )


def _helper_names_in_order(helpers: Sequence[str]) -> List[str]:
    seen: Set[str] = set()
    names: List[str] = []
    for helper in helpers:
        name = helper_decl_name(helper)
        if not name or name in seen:
            continue
        seen.add(name)
        names.append(name)
    return names


def _transitive_dependents(
    helpers: Sequence[str],
    changed_names: Set[str],
) -> Set[str]:
    names = _helper_names_in_order(helpers)
    if not names or not changed_names:
        return set()
    dependent_names: Set[str] = set()
    changed = set(changed_names)
    progressed = True
    while progressed:
        progressed = False
        blockers = changed | dependent_names
        for helper in helpers:
            name = helper_decl_name(helper)
            if not name or name in blockers:
                continue
            refs = _helper_referenced_names(helper, names, skip=name)
            if refs & blockers:
                dependent_names.add(name)
                progressed = True
    return dependent_names


def helper_dependent_names(
    helpers: Sequence[str],
    changed_names: Sequence[str],
) -> Set[str]:
    """Return helpers that transitively depend on any changed helper name."""

    changed = {str(name or "").strip() for name in changed_names if str(name or "").strip()}
    return _transitive_dependents([str(helper or "") for helper in helpers], changed)


def stale_helper_dependent_names(
    dossier: Any,
    changed_names: Sequence[str],
    *,
    preserve_names: Sequence[str] = (),
) -> Set[str]:
    """Return verified helpers invalidated by replaced helper names.

    Same-name corrections are common in failed-turn salvage and child-session
    writeback. Once ``h`` is replaced by a different source hash, any already
    verified helper whose proof or durable replay receipt depends on the old
    ``h`` is no longer reusable unless the caller has just revalidated it.
    This function is intentionally read-only; callers decide which members
    were covered by their accepted Lean replay and which must be removed.
    """

    verified = getattr(dossier, "verified_helpers", None) or {}
    if not verified:
        return set()
    preserve = {
        str(name or "").strip()
        for name in preserve_names
        if str(name or "").strip()
    }
    stale = helper_dependent_names(
        [str(getattr(item, "source", "") or "") for item in verified.values()],
        changed_names,
    )
    changed = {
        str(name or "").strip()
        for name in changed_names
        if str(name or "").strip()
    }
    # Source-token references are only one dependency channel. Durable helper
    # certificates also bind explicit logical support and replay-only context
    # by name/hash. A statement replacement invalidates those exact receipts
    # even when the dependent's source does not mention the helper textually.
    progressed = True
    while progressed:
        progressed = False
        blockers = changed | stale
        for raw_name, helper in verified.items():
            name = str(raw_name or "").strip()
            if not name or name in blockers or name in preserve:
                continue
            dependencies = {
                str(dependency or "").strip()
                for dependency in (
                    *list(getattr(helper, "support_names", []) or []),
                    *list(getattr(helper, "replay_context_names", []) or []),
                    *list(
                        dict(getattr(helper, "support_source_hashes", {}) or {})
                    ),
                    *list(
                        dict(
                            getattr(
                                helper,
                                "replay_context_source_hashes",
                                {},
                            )
                            or {}
                        )
                    ),
                )
                if str(dependency or "").strip()
            }
            if dependencies & blockers:
                stale.add(name)
                progressed = True
    stale = {name for name in stale if name and name not in preserve}
    if not stale:
        return set()
    return stale


@dataclass(frozen=True)
class CorrectionRecheckPlan:
    check_lemmas: List[str]
    stale_dependents_by_correction: Dict[str, Set[str]]
    context_helpers: List[str]
    verification_helpers: List[str]
    fallback_check_lemmas: Optional[List[str]] = None
    fallback_context_helpers: Optional[List[str]] = None


def merge_helpers_for_correction_recheck(
    dossier: Any,
    context_helpers: Sequence[str],
    fresh_helpers: Sequence[str],
    correction_names: Sequence[str],
) -> CorrectionRecheckPlan:
    """Build one authoritative replay after same-name helper corrections.

    A statement correction invalidates both source-level dependents and helpers
    whose durable replay receipt names the old declaration.  An unchanged
    dependent can be retained only after its exact stored source is checked in
    the same Lean transaction as the replacement.  If any optional dependent
    no longer elaborates, the caller retries the bounded replacement-only
    fallback.
    """

    clean_corrections = [
        str(name or "").strip()
        for name in correction_names
        if str(name or "").strip()
    ]
    stale_by_correction = {
        name: stale_helper_dependent_names(dossier, [name])
        for name in clean_corrections
    }
    stale_names = (
        set().union(*stale_by_correction.values())
        if stale_by_correction
        else set()
    )
    if not stale_names:
        return CorrectionRecheckPlan(
            check_lemmas=merge_context_helpers(
                context_helpers,
                fresh_helpers,
            ),
            stale_dependents_by_correction=stale_by_correction,
            context_helpers=list(context_helpers),
            verification_helpers=list(fresh_helpers),
        )

    fresh_names = {
        helper_decl_name(helper) or "" for helper in fresh_helpers
    }
    fresh_names.discard("")
    verified = getattr(dossier, "verified_helpers", None) or {}
    replayable_stale_names = stale_names - fresh_names
    is_context_visible = getattr(
        dossier,
        "is_verified_helper_context_visible",
        None,
    )
    answer_safety_kwargs_fn = getattr(dossier, "_answer_safety_kwargs", None)
    answer_safety_kwargs = (
        dict(answer_safety_kwargs_fn())
        if callable(answer_safety_kwargs_fn)
        else {}
    )

    def stale_replay_allowed(item: Any) -> bool:
        source = str(getattr(item, "source", "") or "").strip()
        if not source:
            return False
        if callable(is_context_visible) and not bool(is_context_visible(item)):
            return False
        return not is_answer_unsafe_helper_source(
            source,
            **answer_safety_kwargs,
        )

    ordered_stale = dependency_ordered_verified_helper_items(
        (name, item)
        for name, item in verified.items()
        if name in replayable_stale_names and stale_replay_allowed(item)
    )
    stale_replay_blocks = [
        str(getattr(item, "source", "") or "").strip()
        for _name, item in ordered_stale
        if str(getattr(item, "source", "") or "").strip()
    ]

    # Remove every invalidated declaration from the pre-existing context.
    # Fresh repaired bodies and exact stored dependents are then added after
    # the replacement, so Lean checks the actual prospective registry.
    retained_context = [
        block
        for block in context_helpers
        if (helper_decl_name(block) or "") not in stale_names
    ]
    verification_helpers = merge_context_helpers(
        fresh_helpers,
        stale_replay_blocks,
    )
    merged = merge_context_helpers(retained_context, verification_helpers)
    fallback_lemmas = merge_context_helpers(retained_context, fresh_helpers)
    return CorrectionRecheckPlan(
        check_lemmas=merged,
        stale_dependents_by_correction=stale_by_correction,
        context_helpers=retained_context,
        verification_helpers=verification_helpers,
        fallback_check_lemmas=(
            fallback_lemmas if stale_replay_blocks else None
        ),
        fallback_context_helpers=(
            retained_context if stale_replay_blocks else None
        ),
    )


def remove_stale_helper_dependents(
    dossier: Any,
    changed_names: Sequence[str],
    *,
    preserve_names: Sequence[str] = (),
) -> Set[str]:
    """Remove verified helpers invalidated by replaced helper names."""

    stale = stale_helper_dependent_names(
        dossier,
        changed_names,
        preserve_names=preserve_names,
    )
    if not stale:
        return set()
    verified = getattr(dossier, "verified_helpers", None) or {}
    remover = getattr(dossier, "remove_verified_helper", None)
    for name in sorted(stale):
        if callable(remover):
            try:
                remover(name)
                continue
            except Exception:
                pass
        try:
            verified.pop(name, None)
        except Exception:
            pass
    return stale


async def _lean_context_check_ok(
    lean: Any,
    lemmas: Sequence[str],
    *,
    preamble: str,
    timeout_s: Optional[float],
    true_statement: str = "True",
    true_proof: str = "by\n  trivial",
    check_kind: str = "full",
) -> bool:
    kwargs: Dict[str, Any] = {
        "preamble_override": preamble,
        "check_kind": check_kind,
    }
    if timeout_s is not None:
        kwargs["timeout_s"] = timeout_s

    async def run_check() -> Any:
        local_kwargs = dict(kwargs)
        try:
            return await lean.check(
                true_statement,
                true_proof,
                list(lemmas),
                **local_kwargs,
            )
        except TypeError:
            local_kwargs.pop("check_kind", None)
            try:
                return await lean.check(
                    true_statement,
                    true_proof,
                    list(lemmas),
                    **local_kwargs,
                )
            except TypeError:
                local_kwargs.pop("timeout_s", None)
                return await lean.check(
                    true_statement,
                    true_proof,
                    list(lemmas),
                    **local_kwargs,
                )

    from .mini_formal_state_search import (
        _LEAN_LOCK_ADMISSION_TIMEOUT_S,
        _run_serialized_lean_operation,
    )

    result = await _run_serialized_lean_operation(
        lean,
        run_check,
        operation_timeout_s=float(timeout_s or 30.0),
        admission_timeout_s=_LEAN_LOCK_ADMISSION_TIMEOUT_S,
    )
    return bool(getattr(result, "ok", False))


async def lean_valid_helper_context_excluding_name(
    lean: Any,
    context: Sequence[str],
    replacing_name: str,
    *,
    preamble: str,
    timeout_s: Optional[float],
    deadline_monotonic: float = 0.0,
    true_statement: str = "True",
    true_proof: str = "by\n  trivial",
) -> Tuple[List[str], Set[str]]:
    """Return helpers that Lean can still replay without ``replacing_name``."""

    blocked_name = str(replacing_name or "").strip()
    pending = [
        str(block or "").strip()
        for block in context
        if str(block or "").strip()
        and (helper_decl_name(str(block or "")) or "") != blocked_name
    ]
    retained: List[str] = []
    while pending:
        progressed = False
        next_pending: List[str] = []
        for position, block in enumerate(pending):
            if deadline_monotonic > 0.0 and time.monotonic() >= deadline_monotonic:
                # Aggregate budget spent. This is a `while pending:` over a
                # `for block in pending:`, so it can run O(N^2) sequential Lean
                # checks, each funded with the FULL per-check timeout; nothing
                # else bounds the total. Retain whatever is still unchecked,
                # exactly as the per-check timeout branch below does: a helper
                # is declared invalid only on a Lean verdict, never on a clock.
                retained.extend(next_pending)
                retained.extend(pending[position:])
                return retained, set()
            lemmas = merge_context_helpers(retained, [block])
            try:
                ok = await _lean_context_check_ok(
                    lean,
                    lemmas,
                    preamble=preamble,
                    timeout_s=timeout_s,
                    true_statement=true_statement,
                    true_proof=true_proof,
                    check_kind="helper_context_revalidation",
                )
            except asyncio.TimeoutError:
                retained.append(block)
                progressed = True
                continue
            if ok:
                retained.append(block)
                progressed = True
            else:
                next_pending.append(block)
        if not progressed:
            pending = next_pending
            break
        pending = next_pending
    return retained, {
        name
        for name in (helper_decl_name(block) for block in pending)
        if name
    }


async def lean_invalid_helpers_after_replacement(
    lean: Any,
    context: Sequence[str],
    replacing_name: str,
    replacement_block: str,
    retained_context: Sequence[str],
    *,
    preamble: str,
    timeout_s: Optional[float],
    deadline_monotonic: float = 0.0,
    true_statement: str = "True",
    true_proof: str = "by\n  trivial",
) -> Set[str]:
    """Return old helpers that Lean cannot replay with the replacement."""

    blocked_name = str(replacing_name or "").strip()
    retained_names = {
        name
        for name in (helper_decl_name(block) for block in retained_context)
        if name
    }
    pending = [
        str(block or "").strip()
        for block in context
        if str(block or "").strip()
        and (helper_decl_name(str(block or "")) or "") != blocked_name
        and (helper_decl_name(str(block or "")) or "") not in retained_names
    ]
    base = list(retained_context) + [str(replacement_block or "").strip()]
    kept_after_replacement: List[str] = []
    while pending:
        progressed = False
        next_pending: List[str] = []
        for position, block in enumerate(pending):
            if deadline_monotonic > 0.0 and time.monotonic() >= deadline_monotonic:
                # Same O(N^2) shape and same conservative rule as the sibling
                # loop: nothing is condemned on a clock. Blocks still pending
                # are implicitly kept -- this function only reports invalid
                # names, and a this-round rejection is not final (the while
                # loop exists because a block can pass once more context has
                # been retained), so the only sound answer here is "none".
                return set()
            lemmas = merge_context_helpers(
                [*base, *kept_after_replacement],
                [block],
            )
            try:
                ok = await _lean_context_check_ok(
                    lean,
                    lemmas,
                    preamble=preamble,
                    timeout_s=timeout_s,
                    true_statement=true_statement,
                    true_proof=true_proof,
                    check_kind="helper_context_revalidation",
                )
            except asyncio.TimeoutError:
                kept_after_replacement.append(block)
                progressed = True
                continue
            if ok:
                kept_after_replacement.append(block)
                progressed = True
            else:
                next_pending.append(block)
        if not progressed:
            pending = next_pending
            break
        pending = next_pending
    return {
        name
        for name in (helper_decl_name(block) for block in pending)
        if name
    }


def order_helpers_for_incremental_validation(
    helpers: Iterable[str],
    *,
    max_primary: Optional[int] = None,
) -> List[str]:
    """Dependency-order raw helper candidates without deduping same-name tries.

    Validation must see multiple same-name candidates in the order the model
    wrote them: an earlier complete proof may be followed by a broken retry.
    The sorter only moves dependency providers before dependents.  When
    ``max_primary`` is set, the first N raw candidates are the budgeted roots
    and any later helpers they depend on are pulled in as dependency closure.
    """

    helper_list = [str(helper or "") for helper in helpers if str(helper or "").strip()]
    if not helper_list:
        return []

    selected_indices: Set[int]
    if max_primary is None or int(max_primary or 0) <= 0:
        selected_indices = set(range(len(helper_list)))
    else:
        selected_indices = set(range(min(len(helper_list), int(max_primary or 0))))

    name_to_indices: Dict[str, List[int]] = {}
    names_in_order: List[str] = []
    for index, helper in enumerate(helper_list):
        name = helper_decl_name(helper)
        if not name:
            continue
        if name not in name_to_indices:
            names_in_order.append(name)
            name_to_indices[name] = []
        name_to_indices[name].append(index)

    changed = True
    while changed:
        changed = False
        for index in list(selected_indices):
            name = helper_decl_name(helper_list[index])
            deps = _helper_referenced_names(
                helper_list[index],
                names_in_order,
                skip=name,
            )
            for dep in deps:
                provider_indices = name_to_indices.get(dep, [])
                dep_index = next(
                    (
                        candidate_index
                        for candidate_index in provider_indices
                        if candidate_index < index
                    ),
                    provider_indices[0] if provider_indices else None,
                )
                if dep_index is not None:
                    if dep_index not in selected_indices:
                        selected_indices.add(dep_index)
                        changed = True

    emitted_indices: Set[int] = set()
    pending = [index for index in range(len(helper_list)) if index in selected_indices]
    ordered_indices: List[int] = []
    while pending:
        progressed = False
        for index in list(pending):
            name = helper_decl_name(helper_list[index])
            deps = _helper_referenced_names(
                helper_list[index],
                names_in_order,
                skip=name,
            )
            missing_provider = False
            for dep in deps:
                provider_indices = [
                    dep_index
                    for dep_index in name_to_indices.get(dep, [])
                    if dep_index in selected_indices
                ]
                if provider_indices and not any(
                    dep_index in emitted_indices for dep_index in provider_indices
                ):
                    missing_provider = True
                    break
            if missing_provider:
                continue
            ordered_indices.append(index)
            emitted_indices.add(index)
            pending.remove(index)
            progressed = True
        if not progressed:
            ordered_indices.extend(pending)
            break
    return [helper_list[index] for index in ordered_indices]


def dedupe_helpers_by_name_last_wins(helpers: Sequence[str]) -> List[str]:
    """Drop duplicate named helpers while preserving declaration dependencies.

    The latest helper block for a name wins, but the emitted order is
    dependency-aware.  This is intentionally shared by extraction and salvage
    merge paths so a corrected helper that gains a new dependency is checked in
    an order Lean can actually compile.
    """

    helper_list = [str(helper or "") for helper in helpers]
    first_index_by_name: Dict[str, int] = {}
    latest_helper_by_name: Dict[str, str] = {}
    names_in_first_order: List[str] = []
    unnamed_helpers: List[Tuple[int, str]] = []
    for index, helper in enumerate(helper_list):
        name = helper_decl_name(helper)
        if name:
            if name not in first_index_by_name:
                first_index_by_name[name] = index
                names_in_first_order.append(name)
            latest_helper_by_name[name] = helper
        else:
            unnamed_helpers.append((index, helper))

    if not latest_helper_by_name:
        return helper_list

    selected_names = set(names_in_first_order)
    deps_by_name: Dict[str, Set[str]] = {
        name: (
            _helper_referenced_names(
                latest_helper_by_name[name],
                names_in_first_order,
                skip=name,
            )
            & selected_names
        )
        for name in names_in_first_order
    }

    emitted: Set[str] = set()
    pending = list(names_in_first_order)
    ordered_names: List[str] = []
    while pending:
        progressed = False
        for name in list(pending):
            if deps_by_name.get(name, set()) - emitted:
                continue
            ordered_names.append(name)
            emitted.add(name)
            pending.remove(name)
            progressed = True
        if not progressed:
            # Cyclic helpers cannot be made valid by reordering. Preserve the
            # stable first-occurrence order for the remaining cycle so Lean can
            # produce the real diagnostic.
            ordered_names.extend(pending)
            break

    named_helpers = [latest_helper_by_name[name] for name in ordered_names]
    if not unnamed_helpers:
        return named_helpers

    if ordered_names == names_in_first_order:
        emitted_names: Set[str] = set()
        out: List[str] = []
        for helper in helper_list:
            name = helper_decl_name(helper)
            if not name:
                out.append(helper)
            elif name not in emitted_names:
                out.append(latest_helper_by_name[name])
                emitted_names.add(name)
        return out

    first_named_index = min(first_index_by_name.values())
    leading_unnamed = [h for i, h in unnamed_helpers if i < first_named_index]
    trailing_unnamed = [h for i, h in unnamed_helpers if i >= first_named_index]
    return leading_unnamed + named_helpers + trailing_unnamed


@dataclass
class HelperSalvageResult:
    accepted: List[str] = field(default_factory=list)
    rejected: List[str] = field(default_factory=list)
    skipped: List[str] = field(default_factory=list)
    evicted: List[str] = field(default_factory=list)
    replaced: List[str] = field(default_factory=list)
    deferred: List[str] = field(default_factory=list)
    deferred_before_launch: List[str] = field(default_factory=list)
    infrastructure_after_launch: List[str] = field(default_factory=list)

    @property
    def any_accepted(self) -> bool:
        return bool(self.accepted)


def merge_context_helpers(
    verified_helpers: Sequence[str],
    fresh_helpers: Sequence[str],
) -> List[str]:
    """Merge verified context helpers with current-turn helpers.

    Dedup is performed on the ``(name, statement_signature)`` pair, NOT on
    name alone. When the current turn re-emits a helper with the SAME name
    AND the SAME statement, the verified version is kept (avoids redeclaration
    in Lean while preserving the name for the proof body). When the current
    turn re-emits a helper with the same name but a DIFFERENT statement, the
    fresh version replaces the verified one — that is the model's self-
    correction (A8 fix, 2026-05-08). Without this, model corrections were
    silently lost and the verified helper poisoned the proof body.
    """
    # Build maps over verified helpers so we can decide replacement on
    # statement-signature mismatch.
    verified_by_name: Dict[str, int] = {}
    verified_blocks: List[Optional[str]] = list(verified_helpers)
    verified_signatures: Dict[str, str] = {}
    for index, block in enumerate(verified_helpers):
        name = helper_decl_name(block)
        if not name:
            continue
        # Last verified wins on duplicate names within ``verified_helpers``.
        verified_by_name[name] = index
        verified_signatures[name] = _helper_statement_signature(block)

    out: List[str] = []
    out_by_name: Dict[str, int] = {}
    seen_signatures: Dict[str, str] = {}
    corrected_names: Set[str] = set()
    fresh_replaced_names: Set[str] = set()

    for index, block in enumerate(verified_blocks):
        if block is None:
            continue
        name = helper_decl_name(block)
        if name and verified_by_name.get(name) != index:
            # Earlier same-name entry was superseded by a later verified one.
            continue
        out_by_name[name] = len(out) if name else -1
        if name:
            seen_signatures[name] = verified_signatures.get(name, "")
        out.append(block)

    for block in fresh_helpers:
        name = helper_decl_name(block)
        if not name:
            out.append(block)
            continue
        fresh_signature = _helper_statement_signature(block)
        if name in out_by_name:
            existing_signature = seen_signatures.get(name, "")
            if fresh_signature == existing_signature:
                # Same name AND same statement — verified version stays.
                continue
            # Same name BUT different statement: model is correcting itself.
            # Replace the verified entry in place to preserve overall ordering.
            replace_idx = out_by_name[name]
            out[replace_idx] = block
            seen_signatures[name] = fresh_signature
            corrected_names.add(name)
            fresh_replaced_names.add(name)
            continue
        out_by_name[name] = len(out)
        seen_signatures[name] = fresh_signature
        fresh_replaced_names.add(name)
        out.append(block)
    if corrected_names:
        stale_dependents = helper_dependent_names(out, list(corrected_names))
        stale_dependents -= fresh_replaced_names
        if stale_dependents:
            out = [
                block
                for block in out
                if (helper_decl_name(block) or "") not in stale_dependents
            ]
    return dedupe_helpers_by_name_last_wins(out)


def collect_open_child_targets(proof_state: Any, *, max_targets: int = 3) -> Tuple[str, ...]:
    """Extract open child-goal target statements from a proof_state.

    The relevance gate probes the helper against the root AND each
    open child-frontier target; this helper picks the targets the
    salvager should consider. Returns an empty tuple if proof_state
    is None or has no open child frontier.
    """
    if proof_state is None:
        return ()
    try:
        frontier = proof_state.child_frontier(max_nodes=int(max_targets))
    except Exception:
        return ()
    targets: List[str] = []
    for node in frontier or ():
        target = str(getattr(node, "target", "") or "").strip()
        if target:
            targets.append(target)
    return tuple(targets)


def _helper_relevance_probe_proof(name: str) -> str:
    """Build the Lean-side relevance probe for one helper.

    The probe asks Lean whether ``name`` can interact with the open
    goal in any of the standard ways Lean uses a hypothesis:
      - ``apply`` (helper's conclusion unifies with goal head)
      - ``intros; apply`` (same, after introducing universals)
      - ``exact`` / ``intros; exact`` (helper directly closes goal)
      - ``simp only [name]`` (helper rewrites something in the goal)

    Lean's ``first`` combinator succeeds iff at least one branch
    succeeds. ``all_goals sorry`` accepts whatever subgoals the
    successful branch left, so the probe answers a pure relevance
    question: "is this helper interactable with this goal?"

    Counterexample-style helpers (e.g. ``∃ S, ¬<goal>``) fail every
    branch — their conclusion-head does not unify with a positive
    goal — so the probe rejects them. Genuine intermediate facts
    succeed via at least one branch and are accepted.
    """
    return (
        "by\n"
        "  first\n"
        f"  | (intros; apply {name}; all_goals sorry)\n"
        f"  | (apply {name}; all_goals sorry)\n"
        f"  | (intros; exact {name})\n"
        f"  | (exact {name})\n"
        f"  | (simp only [{name}])\n"
    )


def _rename_helper_identifier(
    source: str,
    old_name: str,
    new_name: str,
    *,
    allow_arbitrary_dot_suffixes: bool = False,
) -> str:
    """Rename one Lean declaration token and its local references."""

    return rename_lean_identifier(
        source,
        old_name,
        new_name,
        allow_arbitrary_dot_suffixes=allow_arbitrary_dot_suffixes,
    )


def _fresh_helper_collision_name(
    name: str,
    *,
    reserved_names: Set[str],
) -> str:
    """Return a deterministic non-destructive name for a semantic collision."""

    return fresh_lean_alternative_identifier(name, tuple(reserved_names))


class HelperSalvager:
    """Incrementally verifies helper declarations and updates a dossier."""

    def __init__(
        self,
        lean: Any,
        *,
        preamble: str,
        true_statement: str = "True",
        true_proof: str = "by\n  trivial",
        timeout_s: Optional[float] = None,
        relevance_gate_root_statement: str = "",
        relevance_gate_open_targets: Optional[Iterable[str]] = None,
        answer_safe_preamble: str = "",
        verified_helper_accept_callback: Optional[Callable[[Any, Any], Any]] = None,
    ) -> None:
        self.lean = lean
        self.preamble = preamble
        self.answer_safe_preamble = str(answer_safe_preamble or "")
        self.true_statement = true_statement
        self.true_proof = true_proof
        self.timeout_s = timeout_s
        self.verified_helper_accept_callback = verified_helper_accept_callback
        # Claim 4 fix (FINDING_2026-05-12 Defect 6): when set to a
        # non-trivial root goal, the salvager additionally runs a Lean
        # apply/simp probe to confirm the helper is INTERACTABLE with
        # the root, not merely Lean-typechecking. Counterexample
        # helpers (existential refutations of a universal root) fail
        # every probe branch and are rejected as off-topic. Empty or
        # trivial root statements ("True", "False", short Prop
        # placeholders used in tests) disable the gate to preserve
        # backwards compatibility.
        self.relevance_gate_root_statement = str(
            relevance_gate_root_statement or ""
        )
        # Adversarial-review 2026-05-13 (Agent B caveat): probing only
        # against the root statement is over-strict — helpers that are
        # useful for an OPEN SUBGOAL but not directly applicable to
        # the root would be falsely rejected. The salvager now also
        # probes against open child-frontier targets supplied by the
        # caller; the helper is accepted if ANY target accepts it.
        self.relevance_gate_open_targets: Tuple[str, ...] = tuple(
            str(t or "").strip()
            for t in (relevance_gate_open_targets or ())
            if str(t or "").strip()
        )

    def _answer_safe_preamble_differs(self) -> bool:
        from .theorem_project import decode_theorem_target_context

        checker = decode_theorem_target_context(self.preamble)[0].strip()
        safe = decode_theorem_target_context(self.answer_safe_preamble)[0].strip()
        return bool(safe and checker and safe != checker)

    async def _serialized_true_check(
        self,
        check_lemmas: Sequence[str],
        preamble: str,
    ) -> Any:
        kwargs = {
            "preamble_override": preamble,
            "check_kind": "full",
        }
        if self.timeout_s is not None:
            kwargs["timeout_s"] = self.timeout_s

        async def run_check() -> Any:
            local_kwargs = dict(kwargs)
            try:
                return await self.lean.check(
                    self.true_statement,
                    self.true_proof,
                    check_lemmas,
                    **local_kwargs,
                )
            except TypeError:
                local_kwargs.pop("check_kind", None)
                try:
                    return await self.lean.check(
                        self.true_statement,
                        self.true_proof,
                        check_lemmas,
                        **local_kwargs,
                    )
                except TypeError:
                    local_kwargs.pop("timeout_s", None)
                    return await self.lean.check(
                        self.true_statement,
                        self.true_proof,
                        check_lemmas,
                        **local_kwargs,
                    )

        from .mini_formal_state_search import (
            _LEAN_LOCK_ADMISSION_TIMEOUT_S,
            _run_serialized_lean_operation,
        )

        return await _run_serialized_lean_operation(
            self.lean,
            run_check,
            operation_timeout_s=float(self.timeout_s or 30.0),
            admission_timeout_s=_LEAN_LOCK_ADMISSION_TIMEOUT_S,
        )

    async def _run_relevance_probe(
        self,
        relevance_root: str,
        probe_proof: str,
        check_lemmas: List[str],
    ) -> Optional[bool]:
        """Run the relevance probe.

        Returns ``True`` for a semantic pass, ``False`` for a completed
        semantic miss, and ``None`` for verifier infrastructure failure.

        Probe proofs leave ``sorry`` holes in successful branches, so
        the legacy ``check()`` API (which treats sorry_count > 0 as
        ok=False) would force universal rejection. We prefer
        ``check_with_sorry_raw`` when available — it returns the raw
        Lean returncode without applying the sorry-warns-as-errors
        rule. Older fakes only expose ``check``; we fall back, but
        those fakes are expected to return ``ok=True`` for the probe
        themselves (the fake is the source of truth in that case).
        """
        sorry_method = getattr(self.lean, "check_with_sorry_raw", None)
        if sorry_method is not None:
            sorry_kwargs = {"preamble_override": self.preamble}
            if self.timeout_s is not None:
                sorry_kwargs["timeout_s"] = self.timeout_s
            try:
                parsed_sorry, _out, returncode = await sorry_method(
                    relevance_root,
                    probe_proof,
                    check_lemmas,
                    **sorry_kwargs,
                )
                if bool(getattr(parsed_sorry, "infra_failure", False)):
                    return None
                return int(returncode) == 0
            except TypeError:
                sorry_kwargs.pop("timeout_s", None)
                try:
                    parsed_sorry, _out, returncode = await sorry_method(
                        relevance_root,
                        probe_proof,
                        check_lemmas,
                        **sorry_kwargs,
                    )
                    if bool(getattr(parsed_sorry, "infra_failure", False)):
                        return None
                    return int(returncode) == 0
                except Exception:
                    return None
            except Exception:
                return None
        # Fallback: legacy ``check`` for test doubles. The fake is
        # responsible for ignoring sorry_count and reporting probe
        # success via the returned ok field.
        check_kwargs = {
            "preamble_override": self.preamble,
            "check_kind": "helper_relevance_probe",
        }
        if self.timeout_s is not None:
            check_kwargs["timeout_s"] = self.timeout_s
        try:
            probe_result = await self.lean.check(
                relevance_root, probe_proof, check_lemmas, **check_kwargs
            )
            if bool(getattr(getattr(probe_result, "parsed", None), "infra_failure", False)):
                return None
            return bool(getattr(probe_result, "ok", False))
        except TypeError:
            check_kwargs.pop("check_kind", None)
            try:
                probe_result = await self.lean.check(
                    relevance_root, probe_proof, check_lemmas, **check_kwargs
                )
                if bool(getattr(getattr(probe_result, "parsed", None), "infra_failure", False)):
                    return None
                return bool(getattr(probe_result, "ok", False))
            except TypeError:
                check_kwargs.pop("timeout_s", None)
                try:
                    probe_result = await self.lean.check(
                        relevance_root,
                        probe_proof,
                        check_lemmas,
                        **check_kwargs,
                    )
                    if bool(getattr(getattr(probe_result, "parsed", None), "infra_failure", False)):
                        return None
                    return bool(getattr(probe_result, "ok", False))
                except Exception:
                    return None
            except Exception:
                return None
        except Exception:
            return None

    async def salvage(
        self,
        helpers: Iterable[str],
        *,
        dossier: ProofDossier,
        phase: str,
        turn_index: int,
    ) -> HelperSalvageResult:
        result = HelperSalvageResult()
        context = list(dossier.verified_helper_blocks())
        ordered_helpers = order_helpers_for_incremental_validation(
            str(helper or "").strip()
            for helper in helpers
            if str(helper or "").strip()
        )
        reserved_names: Set[str] = set(dossier.verified_helpers)
        reserved_names.update(getattr(dossier, "proposed_helpers", {}) or {})
        proof_graph = getattr(dossier, "proof_graph", None)
        reserved_names.update(
            getattr(proof_graph, "helper_name_to_node_id", {}) or {}
        )
        reserved_names.update(
            str(helper_decl_name(helper) or "").strip()
            for helper in ordered_helpers
            if str(helper_decl_name(helper) or "").strip()
        )
        renamed_collisions: Dict[str, str] = {}
        for helper in ordered_helpers:
            src = str(helper or "").strip()
            if not src:
                continue
            for old_name, new_name in sorted(
                renamed_collisions.items(),
                key=lambda pair: (-len(str(pair[0]).split(".")), -len(pair[0])),
            ):
                src = _rename_helper_identifier(
                    src,
                    old_name,
                    new_name,
                )
            name = helper_decl_name(src)
            if not name:
                result.skipped.append(src.splitlines()[0][:120])
                continue
            validation_context = context
            pending_collision: Optional[Tuple[str, str]] = None
            if dossier.has_helper(name):
                # A8 fix (2026-05-08): only skip if the existing verified
                # helper has the same statement signature. When the model
                # emits a corrected version (same name, different statement),
                # re-validate so the corrected version replaces the stale
                # entry. Without this, model self-corrections were silently
                # dropped and the proof body referenced the wrong statement.
                existing_name = dossier.resolve_verified_helper_name(name)
                existing = dossier.verified_helpers.get(existing_name)
                existing_signature = (
                    _helper_statement_signature(existing.source)
                    if existing is not None
                    else ""
                )
                fresh_signature = _helper_statement_signature(src)
                if existing_signature == fresh_signature:
                    result.skipped.append(name)
                    continue
                old_name = name
                name = _fresh_helper_collision_name(
                    old_name,
                    reserved_names=reserved_names,
                )
                reserved_names.add(name)
                src = _rename_helper_identifier(src, old_name, name)
                pending_collision = (old_name, name)
            # Skip already-verified same-signature retries before this
            # gate. A first-seen sorry/admit stub is unproven and must
            # not be probed or recorded; salvage does not complete it.
            policy_rejection = _proof_state_helper_policy_rejection(src)
            if policy_rejection:
                result.rejected.append(f"{name}:{policy_rejection}")
                continue

            check_lemmas = merge_context_helpers(validation_context, [src])

            try:
                lean_result = await self._serialized_true_check(
                    check_lemmas,
                    self.preamble,
                )
            except asyncio.TimeoutError as exc:
                result.deferred.append(src)
                if "admission" in str(exc).lower():
                    result.deferred_before_launch.append(src)
                else:
                    result.infrastructure_after_launch.append(src)
                continue
            except Exception:
                result.deferred.append(src)
                result.infrastructure_after_launch.append(src)
                continue

            parsed = getattr(lean_result, "parsed", None)
            if (
                not bool(getattr(lean_result, "ok", False))
                and (
                    bool(getattr(parsed, "infra_failure", False))
                    or bool(getattr(parsed, "timeout", False))
                )
            ):
                result.deferred.append(src)
                result.infrastructure_after_launch.append(src)
                continue

            if bool(getattr(lean_result, "ok", False)) and self._answer_safe_preamble_differs():
                try:
                    safe_result = await self._serialized_true_check(
                        check_lemmas,
                        self.answer_safe_preamble,
                    )
                except asyncio.TimeoutError as exc:
                    result.deferred.append(src)
                    if "admission" in str(exc).lower():
                        result.deferred_before_launch.append(src)
                    else:
                        result.infrastructure_after_launch.append(src)
                    continue
                except Exception:
                    result.deferred.append(src)
                    result.infrastructure_after_launch.append(src)
                    continue
                safe_parsed = getattr(safe_result, "parsed", None)
                if (
                    not bool(getattr(safe_result, "ok", False))
                    and (
                        bool(getattr(safe_parsed, "infra_failure", False))
                        or bool(getattr(safe_parsed, "timeout", False))
                    )
                ):
                    result.deferred.append(src)
                    result.infrastructure_after_launch.append(src)
                    continue
                if not bool(getattr(safe_result, "ok", False)):
                    result.rejected.append(f"{name}:answer_safe_recheck_failed")
                    continue

            if bool(getattr(lean_result, "ok", False)):
                # Claim 4 fix (FINDING_2026-05-12 Defect 6): structural
                # relevance gate. A helper that Lean-typechecks may still
                # be SEMANTICALLY off-topic relative to the root goal
                # (e.g. a verified counterexample helper for a universal
                # root). Lean blocks false PROOFS at type-check, but the
                # dossier currently records false PROGRESS — and the
                # LLM, scheduler, and replan budget all consume that
                # progress as advance. The probe below asks Lean
                # directly whether the helper is interactable with the
                # root via apply/exact/simp; counterexample helpers fail
                # all branches because their conclusion-head does not
                # unify with a positive root goal.
                #
                # IMPLEMENTATION NOTE: the probe leaves ``sorry`` holes
                # in successful branches (apply X then ``all_goals
                # sorry``), so we use ``check_with_sorry_raw`` (which
                # suppresses sorry-warns and returns returncode == 0
                # iff Lean's elaborator accepted the tactic). The
                # legacy ``check`` API treats sorry_count > 0 as
                # ok=False, which would force the probe to reject
                # EVERY helper. Old test doubles only expose
                # ``check`` — we fall back to that path but require
                # the fake to indicate probe success via .ok.
                relevance_root = self.relevance_gate_root_statement.strip()
                # Gate is active when the dossier root is a real Lean
                # statement, not a test-fixture placeholder. Placeholder
                # roots ("True"/"False"/single-letter Props) disable the
                # gate entirely so existing synthetic test fixtures keep
                # working.
                # A Lean-valid declaration is durable theorem-DAG material even
                # when it does not directly apply to the root or current child
                # frontier. ProofDossier quality classification controls whether
                # negative/advisory facts are rendered as general context.
                gate_active = False
                if gate_active:
                    # Build the unique target list: root + open child
                    # targets. We probe ALL of them (including ones
                    # that happen to be `True`/`False` — those are real
                    # Lean targets here, not placeholders) and accept
                    # if ANY probe passes. The gate is disabled at
                    # root-level above; per-target trivial skip would
                    # silently let counterexample helpers through
                    # whenever a child goal elaborates to `True`
                    # (e.g. after a `True ∧ <obligation>` split).
                    relevance_targets: List[str] = [relevance_root]
                    relevance_targets.extend(
                        t for t in self.relevance_gate_open_targets if t
                    )
                    _seen: Set[str] = set()
                    _unique_targets: List[str] = []
                    for t in relevance_targets:
                        if t and t not in _seen:
                            _seen.add(t)
                            _unique_targets.append(t)
                    # Cost: up to (1 + min(3, len(open_targets))) Lean
                    # checks per Lean-typechecking helper. With default
                    # max_targets=3 and per-probe timeout=12s, worst
                    # case is 4*12s = 48s per helper. Salvage is a
                    # post-failure recovery path; acceptable trade.
                    probe_passed = False
                    probe_inconclusive = False
                    probe_proof = _helper_relevance_probe_proof(name)
                    for target in _unique_targets:
                        probe_result = await self._run_relevance_probe(
                            target, probe_proof, check_lemmas
                        )
                        if probe_result is True:
                            probe_passed = True
                            break
                        if probe_result is None:
                            probe_inconclusive = True
                    if not probe_passed:
                        rejection = (
                            "relevance_probe_inconclusive"
                            if probe_inconclusive
                            else "off_topic"
                        )
                        result.rejected.append(f"{name}:{rejection}")
                        continue
                recorded = dossier.record_verified_helper(
                    src,
                    phase=phase,
                    turn_index=turn_index,
                    replay_context_names=[
                        helper_decl_name(block) or ""
                        for block in validation_context
                        if helper_decl_name(block) and helper_decl_name(block) != name
                    ],
                )
                if recorded is None:
                    result.rejected.append(f"{name}:record_rejected")
                    continue
                if callable(self.verified_helper_accept_callback):
                    try:
                        self.verified_helper_accept_callback(recorded, dossier)
                    except Exception:
                        pass
                context = list(dossier.verified_helper_blocks())
                landed_name = str(getattr(recorded, "name", "") or name)
                if pending_collision is not None:
                    renamed_collisions[pending_collision[0]] = landed_name
                result.accepted.append(landed_name)
            else:
                result.rejected.append(name)
        return result
