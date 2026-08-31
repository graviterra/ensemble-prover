"""Context-scoped tactic-source suppression shared by mini-session actions."""

from __future__ import annotations

from typing import Any, Mapping, Sequence

from ensemble_prover.mini_finset_reindexer import finset_reindexing_context_key
from ensemble_prover.proof_dossier import helper_decl_name, text_hash


SESSION_TACTIC_SOURCE_SUPPRESSION_ATTR = "_tactic_close_source_suppression_records"


def helper_fingerprints(helper_blocks: Sequence[str]) -> tuple[str, ...]:
    """Return stable helper fingerprints for tactic-source context keys."""

    block_by_name = {
        name: str(block or "")
        for block in list(helper_blocks or ())
        for name in [helper_decl_name(str(block or ""))]
        if name
    }
    return tuple(
        f"{name}:{text_hash(block_by_name.get(name, ''))}"
        for name in sorted(block_by_name)
        if str(name or "").strip()
    )


def tactic_source_context_key(
    *,
    source_prefix: str,
    goal_statement: str,
    helper_blocks: Sequence[str] = (),
) -> str:
    """Build the context key used to decide whether a source was exhausted."""

    prefix = str(source_prefix or "").strip()
    goal = " ".join(str(goal_statement or "").split())
    fingerprints = helper_fingerprints(tuple(str(item or "") for item in helper_blocks))
    if prefix == "finset_reindexing":
        return finset_reindexing_context_key(goal, fingerprints)
    helpers = ",".join(fingerprints)
    return f"{goal}|helpers={helpers}"


def tactic_source_suppression_records(session: Any) -> tuple[dict[str, Any], ...]:
    """Return normalized tactic-source suppression records from a session."""

    raw = getattr(session, SESSION_TACTIC_SOURCE_SUPPRESSION_ATTR, ()) or ()
    records: list[dict[str, Any]] = []
    for item in list(raw):
        if not isinstance(item, Mapping):
            continue
        prefix = str(item.get("source_prefix") or "").strip()
        context_key = str(item.get("context_key") or "").strip()
        if not prefix or not context_key:
            continue
        records.append(
            {
                "source_prefix": prefix,
                "context_key": context_key,
                "goal_hash": str(item.get("goal_hash") or "").strip(),
                "helper_fingerprints": [
                    str(value)
                    for value in list(item.get("helper_fingerprints") or ())
                    if str(value or "").strip()
                ],
                "reason": str(item.get("reason") or "exhausted").strip(),
            }
        )
    return tuple(records)


def mark_tactic_source_prefix_exhausted(
    session: Any,
    *,
    source_prefix: str,
    goal_statement: str,
    helper_blocks: Sequence[str] = (),
    reason: str = "exhausted",
) -> None:
    """Record that a tactic source exhausted one exact goal/helper context."""

    prefix = str(source_prefix or "").strip()
    if not prefix:
        return
    blocks = tuple(str(item or "") for item in list(helper_blocks or ()))
    context_key = tactic_source_context_key(
        source_prefix=prefix,
        goal_statement=goal_statement,
        helper_blocks=blocks,
    )
    if not context_key:
        return
    fingerprints = helper_fingerprints(blocks)
    record = {
        "source_prefix": prefix,
        "context_key": context_key,
        "goal_hash": text_hash(" ".join(str(goal_statement or "").split())),
        "helper_fingerprints": list(fingerprints),
        "reason": str(reason or "exhausted").strip(),
    }
    records = list(tactic_source_suppression_records(session))
    if not any(
        str(existing.get("source_prefix") or "") == prefix
        and str(existing.get("context_key") or "") == context_key
        for existing in records
    ):
        records.append(record)
    try:
        setattr(session, SESSION_TACTIC_SOURCE_SUPPRESSION_ATTR, records)
    except Exception:
        pass


def tactic_source_prefix_exhausted_for_context(
    session: Any,
    *,
    source_prefix: str,
    goal_statement: str,
    helper_blocks: Sequence[str] = (),
) -> bool:
    """Return True when a source was exhausted for this exact context."""

    prefix = str(source_prefix or "").strip()
    if not prefix:
        return False
    return source_prefix_exhausted_in_records(
        tactic_source_suppression_records(session),
        source_prefix=prefix,
        goal_statement=goal_statement,
        helper_blocks=helper_blocks,
    )


def source_prefix_exhausted_in_records(
    records: Sequence[Mapping[str, Any]],
    *,
    source_prefix: str,
    goal_statement: str,
    helper_blocks: Sequence[str] = (),
) -> bool:
    """Return True when suppression records exhaust one exact source context."""

    prefix = str(source_prefix or "").strip()
    if not prefix:
        return False
    context_key = tactic_source_context_key(
        source_prefix=prefix,
        goal_statement=goal_statement,
        helper_blocks=tuple(str(item or "") for item in list(helper_blocks or ())),
    )
    return any(
        str(record.get("source_prefix") or "") == prefix
        and str(record.get("context_key") or "") == context_key
        for record in list(records or ())
        if isinstance(record, Mapping)
    )


def excluded_tactic_source_prefixes_for_context(
    session: Any,
    *,
    goal_statement: str,
    helper_blocks: Sequence[str] = (),
    source_prefixes: Sequence[str] = ("finset_reindexing",),
) -> tuple[str, ...]:
    """Return source prefixes that should be suppressed in this context."""

    return excluded_tactic_source_prefixes_from_records(
        tactic_source_suppression_records(session),
        goal_statement=goal_statement,
        helper_blocks=helper_blocks,
        source_prefixes=source_prefixes,
    )


def excluded_tactic_source_prefixes_from_records(
    records: Sequence[Mapping[str, Any]],
    *,
    goal_statement: str,
    helper_blocks: Sequence[str] = (),
    source_prefixes: Sequence[str] = ("finset_reindexing",),
) -> tuple[str, ...]:
    """Return suppressed source prefixes for a statement/helper context."""

    excluded: list[str] = []
    for prefix in list(source_prefixes or ()):
        clean = str(prefix or "").strip()
        if not clean:
            continue
        if source_prefix_exhausted_in_records(
            records,
            source_prefix=clean,
            goal_statement=goal_statement,
            helper_blocks=helper_blocks,
        ):
            excluded.append(clean)
    return tuple(dict.fromkeys(excluded))


__all__ = [
    "SESSION_TACTIC_SOURCE_SUPPRESSION_ATTR",
    "excluded_tactic_source_prefixes_for_context",
    "excluded_tactic_source_prefixes_from_records",
    "helper_fingerprints",
    "mark_tactic_source_prefix_exhausted",
    "source_prefix_exhausted_in_records",
    "tactic_source_context_key",
    "tactic_source_prefix_exhausted_for_context",
    "tactic_source_suppression_records",
]
