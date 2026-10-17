"""Bounded observation of operator-supplied independent committed source copies.

This adapter never opens a canonical store or restores an executable checkpoint.
``offline=True`` is an explicit assertion that the selected files are independent,
quiescent copies or committed exports. It is not permission to inspect a live run.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import json
import math
import os
from pathlib import Path
import sqlite3
import stat
import time
from typing import Any

from .policy import AccessContext, HostPolicy, context_binding
from .references import (
    ContextRef,
    GraphRef,
    HelperRef,
    ProjectionError,
    QuestionRef,
    SourceRef,
    TargetRef,
    canonical_json,
    sha256_digest,
)

EXTRACTION_VERSION = "offline-owners-v1"
_APPLICATION_ID = 0x52534348
_SCHEMA_VERSIONS = frozenset(range(1, 9))
_HIDDEN_FIELDS = frozenset(
    {
        "preamble",
        "lean_preamble",
        "checker_preamble",
        "checker_only_preamble",
        "verification_preamble",
        "official_answer",
        "official_answer_payload",
        "hidden_answer",
        "hidden_checker",
        "checker_only",
        "solution_payload",
    }
)
_HIDDEN_POLICIES = frozenset({"hidden", "private", "checker_only", "checker-only"})
_PROOF_SEMANTIC_FIELDS = frozenset({
    "antecedents", "premises", "hypotheses", "assumptions", "preconditions",
    "contract", "scope", "alternatives", "branches", "goal_statement", "goal_id",
    "branch_frame_id", "context_hash", "attempt", "attempt_id", "root_lineage",
    "root_statement", "theorem_name", "revision", "statement_environment",
    "statement_environment_hash", "statement", "node_id", "name", "source", "source_hash",
    "target", "working_target", "originating_dispatch", "dispatch", "frame", "environment",
    "contract_identity", "contract_identity_environment_hash", "verification_environment_hash",
    "contract_identity_statement_key", "contract_identity_evidence_receipt", "contract_display_statement",
    "contract_binder_evidence_receipt", "open_premise_statement_keys",
    "open_premise_statements", "closed_open_premise_statements", "contract_proof_binder_types",
    "contract_binder_sorts", "support_names", "support_source_hashes", "replay_context_names",
    "replay_context_source_hashes", "visibility", "visibility_policy", "answer_visibility",
    "verified_helper_visibility_policy",
})
_LIST_ITEM = object()
_MAP_VALUE = object()
_TABLES = {
    "revisions": ("claim_id", "revision", "spec", "created_at", "cause"),
    "evidence": ("evidence_id", "claim_id", "revision", "record"),
    "reviews": ("review_id", "claim_id", "revision", "record"),
    "contributions": ("contribution_id", "claim_id", "revision", "record"),
    "operations": ("operation_id", "claim_id", "revision", "record"),
    "discovery_jobs": ("job_id", "status", "record"),
    "frontier_records": (
        "record_id",
        "kind",
        "owner_id",
        "target_id",
        "status",
        "revision",
        "record",
    ),
}


class _Unavailable(ValueError):
    pass


@dataclass(frozen=True)
class _ConversationMapping:
    """Inert entries for an optional durable mapping with non-JSON keys."""

    entries: tuple[tuple[Any, Any], ...]


@dataclass
class _Budget:
    max_bytes: int
    deadline: float
    consumed: int = 0

    def check(self, size: int = 0) -> None:
        if time.monotonic() >= self.deadline:
            raise _Unavailable("deadline_exceeded")
        self.consumed += size
        if self.consumed > self.max_bytes:
            raise _Unavailable("byte_limit_exceeded")

    def account(self, value: Any) -> None:
        """Charge projected JSON before retaining it, with bounded scratch space."""
        self.check()
        if isinstance(value, str):
            self.check(2)
            for offset in range(0, len(value), 4096):
                piece = json.dumps(value[offset : offset + 4096], ensure_ascii=False)
                self.check(len(piece[1:-1].encode("utf-8")))
        elif isinstance(value, dict):
            self.check(2 + max(0, len(value) - 1) + len(value))
            for key, item in value.items():
                self.account(key)
                self.account(item)
        elif isinstance(value, list):
            self.check(2 + max(0, len(value) - 1))
            for item in value:
                self.account(item)
        else:
            self.check(len(canonical_json(value)))


def _stamp(info: os.stat_result) -> tuple[int, ...]:
    return info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns


def _read_file(path: Path, budget: _Budget) -> tuple[bytes, tuple[int, ...]]:
    """Read one regular, unaliased copy and reject replacement during extraction."""
    budget.check()
    absolute = path.absolute()
    if any(part.is_symlink() for part in (absolute, *absolute.parents)):
        raise _Unavailable("unsafe_source_alias")
    descriptor = os.open(absolute, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(descriptor, "rb") as stream:
        before = os.fstat(stream.fileno())
        if not stat.S_ISREG(before.st_mode) or before.st_nlink != 1:
            raise _Unavailable("unsafe_source_alias")
        if before.st_size > budget.max_bytes - budget.consumed:
            raise _Unavailable("byte_limit_exceeded")
        pieces = []
        while True:
            budget.check()
            piece = stream.read(min(65536, budget.max_bytes - budget.consumed + 1))
            if not piece:
                break
            budget.check(len(piece))
            pieces.append(piece)
        after = os.fstat(stream.fileno())
    if _stamp(before) != _stamp(after) or _stamp(absolute.stat()) != _stamp(before):
        raise _Unavailable("source_changed")
    return b"".join(pieces), _stamp(before)


def _json(data: bytes | str) -> Any:
    from ..json_pages import strict_loads

    return strict_loads(data.encode("utf-8") if isinstance(data, str) else data)


def _opaque(value: Any, budget: _Budget | None = None) -> Any:
    """Remove checker-only fields without making their values resolver endpoints."""
    if budget is not None:
        budget.check()
    if isinstance(value, dict):
        if not _visible(value, budget):
            return None
        return {
            key: _opaque(item, budget)
            for key, item in value.items()
            if key.lower() not in _HIDDEN_FIELDS and _visible(item, budget)
        }
    if isinstance(value, list):
        return [_opaque(item, budget) for item in value if _visible(item, budget)]
    return value


def _contains_hidden(value: Any, budget: _Budget | None = None) -> bool:
    if budget is not None:
        budget.check()
    if _marked_hidden(value):
        return True
    if isinstance(value, dict):
        return any(_contains_hidden(item, budget) for key, item in value.items()
                   if key.lower() not in _HIDDEN_FIELDS)
    if isinstance(value, list):
        return any(_contains_hidden(item, budget) for item in value)
    return False


def _visible(value: Any, budget: _Budget | None = None) -> bool:
    if budget is not None:
        budget.check()
    if not isinstance(value, dict):
        return True
    return not _marked_hidden(value) and not any(
        _contains_hidden(value[key], budget)
        for key in (
            "metadata", "antecedents", "premises", "hypotheses", "assumptions",
            "preconditions", "contract", "scope", "alternatives", "branches",
        )
        if key in value
    )


def _marked_hidden(value: Any) -> bool:
    """Read only this record's marker; recursive scans visit descendants once."""
    if not isinstance(value, dict):
        return False
    return any(
        str(value.get(key, "")).lower() in _HIDDEN_POLICIES
        for key in (
            "visibility",
            "visibility_policy",
            "answer_visibility",
            "verified_helper_visibility_policy",
        )
    )


def _proof_value_visible(value: Any, budget: _Budget, *, required: bool = False) -> bool:
    """Preserve semantic values in full while allowing optional checker fields."""
    budget.check()
    marker_record = value
    if isinstance(value, _ConversationMapping):
        marker_record = {}
        for key, item in value.entries:
            budget.check()
            if isinstance(key, str):
                marker_record[key] = item
    if _marked_hidden(marker_record):
        return False
    if isinstance(value, (dict, _ConversationMapping)):
        entries = value.items() if isinstance(value, dict) else value.entries
        for key, item in entries:
            budget.check()
            if not isinstance(key, str):
                if (not _proof_value_visible(key, budget, required=required)
                        or not _proof_value_visible(item, budget, required=required)):
                    return False
                continue
            if key.lower() in _HIDDEN_FIELDS:
                if required:
                    return False
                continue
            if not _proof_value_visible(
                item, budget, required=(
                    required or key.startswith("verified_helper_") or key in _PROOF_SEMANTIC_FIELDS
                ),
            ):
                return False
    elif isinstance(value, list):
        return all(_proof_value_visible(item, budget, required=required) for item in value)
    return True


def _json_context_value(value: Any, budget: _Budget) -> bool:
    """Optional durable mappings cannot become invented reference identities."""
    budget.check()
    if isinstance(value, _ConversationMapping):
        return False
    if isinstance(value, dict):
        return all(_json_context_value(item, budget) for item in value.values())
    if isinstance(value, list):
        return all(_json_context_value(item, budget) for item in value)
    return True


def _mentions_identity(value: Any, identities: set[str], budget: _Budget) -> bool:
    """Retain whole records when their explicit references remain visible."""
    budget.check()
    if not identities or not _visible(value, budget):
        return False
    if isinstance(value, _ConversationMapping):
        return any(
            _mentions_identity(key, identities, budget)
            or _mentions_identity(item, identities, budget)
            for key, item in value.entries
            if not isinstance(key, str) or key.lower() not in _HIDDEN_FIELDS
        )
    if isinstance(value, str):
        return value in identities
    if isinstance(value, dict):
        return any(
            key in identities or _mentions_identity(item, identities, budget)
            for key, item in value.items() if key.lower() not in _HIDDEN_FIELDS
        )
    if isinstance(value, list):
        return any(_mentions_identity(item, identities, budget) for item in value)
    return False


def _source_ref(namespace: str, digest: str, item: str) -> dict[str, Any]:
    return SourceRef(namespace=namespace, content_digest=digest, item=item).to_dict()


def _authorize(
    policy: HostPolicy, context: AccessContext, dependency: dict[str, Any]
) -> None:
    if not policy.authorize(dependency, context):
        raise ProjectionError("not_authorized")


def _decode_conversation(value: Any, budget: _Budget) -> dict[str, Any]:
    """Read nested durable containers as inert JSON, never restored objects."""
    def decode(item: Any, depth: int) -> Any:
        budget.check()
        if depth > 64:
            raise _Unavailable("unsupported_conversation_schema")
        if isinstance(item, list):
            return [decode(child, depth + 1) for child in item]
        if not isinstance(item, dict):
            return item
        kind = item.get("value_type")
        if isinstance(kind, str) and kind in {"dict", "tuple", "set", "frozenset"}:
            entries = item.get("items")
            if set(item) != {"value_type", "items"} or not isinstance(entries, list):
                raise _Unavailable("unsupported_conversation_schema")
            if kind != "dict":
                return [decode(child, depth + 1) for child in entries]
            pairs: list[tuple[Any, Any]] = []
            seen: set[bytes] = set()
            for pair in entries:
                budget.check()
                if not isinstance(pair, list) or len(pair) != 2:
                    raise _Unavailable("unsupported_conversation_schema")
                key_bytes = canonical_json(pair[0])
                budget.check(len(key_bytes))
                if key_bytes in seen:
                    raise _Unavailable("unsupported_conversation_schema")
                seen.add(key_bytes)
                pairs.append((decode(pair[0], depth + 1), decode(pair[1], depth + 1)))
            if all(isinstance(key, str) for key, _ in pairs):
                return dict(pairs)
            if depth == 0:
                raise _Unavailable("unsupported_conversation_schema")
            return _ConversationMapping(tuple(pairs))
        # Durable value-class wrappers stay dictionaries. Recursively inspect
        # their fields without importing a class or calling a constructor.
        return {key: decode(child, depth + 1) for key, child in item.items()}

    if not isinstance(value, dict):
        return {}
    decoded = decode(value, 0)
    if not isinstance(decoded, dict):
        raise _Unavailable("unsupported_conversation_schema")
    return decoded


def _proof_values(
    record: dict[str, Any],
    namespace: str,
    digest: str,
    policy: HostPolicy,
    context: AccessContext,
    budget: _Budget,
) -> dict[str, Any]:
    def visible(value: Any) -> bool:
        return _visible(value, budget)

    def opaque(value: Any) -> Any:
        return _opaque(value, budget)

    def complete(value: Any) -> bool:
        # A declaration, contract, or contextual identity is one retained unit.
        # Removing an arbitrary hidden child can change its premises or scope.
        budget.check()
        if not isinstance(value, dict):
            return _proof_value_visible(value, budget, required=True)
        if _marked_hidden(value):
            return False
        for key, item in value.items():
            budget.check()
            if key.lower() in _HIDDEN_FIELDS:
                continue
            if key == "metadata" and isinstance(item, dict):
                if _marked_hidden(item):
                    return False
                # Owner metadata can bind a record's scope or evidence. Keep
                # each non-checker value whole, including unfamiliar fields;
                # nested hidden diagnostics conservatively omit the record.
                for metadata_key, metadata_value in item.items():
                    budget.check()
                    if metadata_key.lower() in _HIDDEN_FIELDS:
                        continue
                    if not _proof_value_visible(metadata_value, budget, required=True):
                        return False
            elif not _proof_value_visible(item, budget, required=True):
                return False
        return True

    if not visible(record):
        return {"sessions": []}
    sessions = record.get("sessions")
    if not isinstance(sessions, dict):
        if isinstance(record.get("dossier"), dict):
            lane = record.get("lane")
            if not _proof_value_visible(lane, budget, required=True):
                return {"sessions": []}
            if lane is not None and not isinstance(lane, str):
                raise _Unavailable("unsupported_proof_schema")
            sessions = {lane or "unknown": record}
        elif "verified_helpers" in record and "root_statement" in record:
            sessions = {"unknown": {"dossier": record}}
        else:
            raise _Unavailable("unsupported_proof_schema")
    projected = []
    attempt = record.get("attempt_id")
    for lane, session in sessions.items():
        budget.check()
        if not isinstance(session, dict) or not isinstance(
            session.get("dossier"), dict
        ):
            raise _Unavailable("unsupported_proof_schema")
        locator = f"sessions/{lane}" if "sessions" in record else "$"
        dossier = session["dossier"]
        if not visible(session) or not visible(dossier):
            continue
        source_refs: list[dict[str, Any]] = []

        raw_conversation = session.get("conversation")
        if not visible(raw_conversation):
            continue
        conversation = _decode_conversation(raw_conversation, budget)
        identity = session.get("identity") or {}
        if not isinstance(identity, dict):
            raise _Unavailable("unsupported_proof_schema")
        owner_identity = identity.get("attempt_identity") or {}
        if not isinstance(owner_identity, dict):
            raise _Unavailable("unsupported_proof_schema")
        scope = {
            "conversation": conversation,
            "identity": identity,
            "attempt": attempt or owner_identity.get("attempt_id"),
            "root_lineage": owner_identity.get("root_lineage", record.get("root_lineage")),
            "root_statement": dossier.get("root_statement", conversation.get("goal_statement")),
            "theorem_name": dossier.get("theorem_name"),
            "revision": session.get("revision"),
            "statement_environment": dossier.get("statement_environment_hash"),
        }
        if not _proof_value_visible(scope, budget):
            continue
        copied_context = [item for key, item in scope.items() if key != "conversation"]
        copied_context.extend((conversation.get("goal_id"), conversation.get("branch_frame_id")))
        if not all(_json_context_value(item, budget) for item in copied_context):
            continue
        scope = opaque(scope)
        conversation = scope["conversation"]
        identity = scope["identity"]
        session_attempt = scope["attempt"]

        def authorize_item(suffix: str) -> dict[str, Any]:
            source = _source_ref(namespace, digest, locator + suffix)
            _authorize(policy, context, source)
            source_refs.append(source)
            return source

        authorize_item("")
        authorize_item("/dossier")
        if raw_conversation is not None:
            authorize_item("/conversation")
        if session.get("identity") is not None:
            authorize_item("/identity")
        graph = dossier.get("proof_graph") or {}
        if not isinstance(graph, dict):
            raise _Unavailable("unsupported_graph_schema")
        if not visible(graph):
            graph = {}
        authorize_item("/dossier/proof_graph")
        raw_helpers = dossier.get("verified_helpers", [])
        if isinstance(raw_helpers, dict):
            raw_helpers = list(raw_helpers.values())
        if not isinstance(raw_helpers, list):
            raise _Unavailable("unsupported_helper_schema")
        raw_nodes = graph.get("nodes", [])
        if not isinstance(raw_nodes, list):
            raise _Unavailable("unsupported_graph_schema")
        helper_nodes = graph.get("helper_name_to_node_id") or {}
        if not isinstance(helper_nodes, dict):
            raise _Unavailable("unsupported_graph_schema")
        for node_id in helper_nodes.values():
            budget.check()
            if not isinstance(node_id, str):
                raise _Unavailable("unsupported_graph_schema")
        hidden_names: set[str] = set()
        hidden_nodes: set[str] = set()
        for helper in raw_helpers:
            budget.check()
            if not isinstance(helper, dict) or not isinstance(helper.get("source"), str):
                raise _Unavailable("unsupported_helper_schema")
            if not complete(helper):
                hidden_names.add(str(helper.get("name", "")))
        for node in raw_nodes:
            budget.check()
            if not isinstance(node, dict):
                raise _Unavailable("unsupported_graph_schema")
            if not complete(node):
                hidden_names.add(str(node.get("name", "")))
                hidden_nodes.add(str(node.get("node_id", "")))
        raw_frames = graph.get("branch_frames", [])
        if not isinstance(raw_frames, (list, dict)):
            raise _Unavailable("unsupported_graph_schema")
        frame_records = raw_frames.values() if isinstance(raw_frames, dict) else raw_frames
        for frame in frame_records:
            budget.check()
            if isinstance(frame, dict) and not complete(frame):
                hidden_nodes.add(str(frame.get("frame_id", "")))
        hidden_names.discard("")
        hidden_nodes.discard("")
        # A support list or branch record can disclose a hidden record even
        # after its own row is omitted. Omit dependent records as complete units;
        # never publish a shortened set of required premises.
        while True:
            before = (len(hidden_names), len(hidden_nodes))
            for name, node_id in helper_nodes.items():
                budget.check()
                if name in hidden_names or node_id in hidden_nodes:
                    hidden_names.add(name)
                    hidden_nodes.add(node_id)
            identities = hidden_names | hidden_nodes
            for helper in raw_helpers:
                budget.check()
                if _mentions_identity(helper, identities, budget):
                    hidden_names.add(str(helper.get("name", "")))
            for node in raw_nodes:
                budget.check()
                if _mentions_identity(node, hidden_names | hidden_nodes, budget):
                    hidden_nodes.add(str(node.get("node_id", "")))
                    hidden_names.add(str(node.get("name", "")))
            for frame in frame_records:
                budget.check()
                if isinstance(frame, dict) and _mentions_identity(
                    frame, hidden_names | hidden_nodes, budget
                ):
                    hidden_nodes.add(str(frame.get("frame_id", "")))
            hidden_names.discard("")
            hidden_nodes.discard("")
            if before == (len(hidden_names), len(hidden_nodes)):
                break
        if graph.get("root_node_id") in hidden_nodes or _mentions_identity(
            conversation, hidden_names | hidden_nodes, budget
        ):
            continue

        def selected_collection(
            value: Any, suffix: str, *, allowed_mirrors: set[str] | None = None,
        ) -> Any:
            authorize_item(suffix)
            if not visible(value):
                return None
            if allowed_mirrors is not None and not isinstance(value, list):
                raise _Unavailable("unsupported_graph_schema")
            if isinstance(value, list):
                selected = []
                seen_mirrors: set[str] = set()
                for index, item in enumerate(value):
                    budget.check()
                    if allowed_mirrors is not None:
                        if (not isinstance(item, str) or item.strip() not in allowed_mirrors
                                or item.strip() in seen_mirrors):
                            continue
                        seen_mirrors.add(item.strip())
                    if not complete(item) or _mentions_identity(
                        item, hidden_names | hidden_nodes, budget
                    ):
                        continue
                    authorize_item(f"{suffix}/{index}")
                    selected.append(opaque(item))
                return selected
            if isinstance(value, dict):
                selected_mapping = {}
                for key, item in value.items():
                    budget.check()
                    if not complete(item) or _mentions_identity(
                        item, hidden_names | hidden_nodes, budget
                    ):
                        continue
                    authorize_item(f"{suffix}/{key}")
                    selected_mapping[key] = opaque(item)
                return selected_mapping
            return opaque(value)

        raw_targets = dossier.get("active_root_targets", [])
        if not isinstance(raw_targets, list):
            raise _Unavailable("unsupported_active_target_schema")
        for item in raw_targets:
            budget.check()
            if not isinstance(item, dict):
                raise _Unavailable("unsupported_active_target_schema")
        active_targets = selected_collection(raw_targets, "/dossier/active_root_targets")
        mirror_statements: set[str] | None = None
        mirror_contracts: set[str] | None = None
        if len(active_targets) != len(raw_targets):
            # These two owner inventories mirror active targets. Once a target
            # is omitted, retain only entries witnessed by a public target;
            # matching statements elsewhere are independent public records.
            from ..proof_dossier import active_root_equivalence_statements

            mirror_statements, mirror_contracts = set(), set()
            for item in active_targets:
                budget.check()
                for field in ("target", "working_target", "kernel_target"):
                    statement = item.get(field)
                    if isinstance(statement, str) and statement.strip():
                        mirror_statements.add(statement.strip())
                contract = item.get("contract_identity")
                if isinstance(contract, str) and contract.strip():
                    mirror_contracts.add(contract.strip())
                hypotheses = item.get("hypotheses") or []
                target_statement = item.get("working_target") or item.get("target")
                if (isinstance(target_statement, str) and isinstance(hypotheses, list)
                        and all(isinstance(hypothesis, str) for hypothesis in hypotheses)):
                    for statement in active_root_equivalence_statements([item]):
                        budget.account(statement)
                        mirror_statements.add(statement)
        active_statement = None
        active_identity = None
        if len(raw_targets) == 1 and len(active_targets) == 1:
            active_statement = active_targets[0].get(
                "working_target"
            ) or active_targets[0].get("target")
            active_identity = active_targets[0].get("contract_identity")
        root_lineage = {
            "owner_identity": scope["root_lineage"],
            "theorem_name": scope["theorem_name"],
            "statement": scope["root_statement"],
            "snapshot_locator": _source_ref(namespace, digest, locator),
        }
        target = TargetRef(
            namespace=namespace,
            root_lineage=root_lineage,
            active_target={
                "status": "recorded" if active_targets else "unassigned",
                "owner_goal_id": conversation.get("goal_id"),
                "statement": active_statement,
                "records": active_targets,
                "snapshot_locator": _source_ref(namespace, digest, locator),
            },
            statement_identity=active_identity,
            revision=scope["revision"],
            frame=conversation.get("branch_frame_id"),
            attempt=session_attempt,
            lane=lane if lane != "unknown" else None,
        ).to_dict()
        verification = ContextRef(
            namespace=namespace,
            statement_environment=scope["statement_environment"],
            verification_context=identity.get("context_hash"),
            digest_algorithm="owner_opaque",
        ).to_dict()
        helpers = []
        for index, helper in enumerate(raw_helpers):
            budget.check()
            if not isinstance(helper, dict) or not isinstance(
                helper.get("source"), str
            ):
                raise _Unavailable("unsupported_helper_schema")
            if not complete(helper) or helper.get("name") in hidden_names:
                continue
            helper = opaque(helper)
            source = _source_ref(
                namespace, digest, f"{locator}/dossier/verified_helpers/{index}"
            )
            _authorize(policy, context, source)
            helper_context = ContextRef(
                namespace=namespace,
                statement_environment=helper.get("contract_identity_environment_hash")
                or None,
                verification_context=helper.get("verification_environment_hash")
                or None,
                digest_algorithm="owner_opaque",
            ).to_dict()
            reference = HelperRef(
                namespace=namespace,
                attempt=session_attempt,
                lane=lane if lane != "unknown" else None,
                helper_name=str(helper.get("name", "")),
                source_digest=sha256_digest(helper["source"].encode("utf-8")),
                contract=helper.get("contract_identity") or None,
                verification_context=helper_context,
                owner_revision=helper.get("revision"),
                snapshot_locator=source,
            ).to_dict()
            helpers.append(
                {
                    "ref": reference,
                    "target": target,
                    "record": helper,
                    "legacy_source_hash": {
                        "algorithm": "legacy:sha256:utf8:16",
                        "value": helper.get("source_hash"),
                    },
                    "origin": {
                        "status": (
                            "recorded"
                            if helper.get("originating_dispatch")
                            else "unknown"
                        ),
                        "dispatch": helper.get("originating_dispatch"),
                    },
                    "applicability": "historical",
                    "usefulness": "unknown",
                }
            )
            budget.account(helpers[-1])
        nodes = []
        for index, node in enumerate(raw_nodes):
            if not isinstance(node, dict):
                raise _Unavailable("unsupported_graph_schema")
            if (
                not complete(node)
                or node.get("name") in hidden_names
                or node.get("node_id") in hidden_nodes
            ):
                hidden_nodes.add(str(node.get("node_id", "")))
                continue
            node = opaque(node)
            source = _source_ref(
                namespace, digest, f"{locator}/dossier/proof_graph/nodes/{index}"
            )
            _authorize(policy, context, source)
            metadata = node.get("metadata") or {}
            reference = GraphRef(
                namespace=namespace,
                node_id=str(node.get("node_id", "")),
                statement=str(node.get("statement", "")),
                frame=metadata.get("branch_frame_id"),
                environment=metadata.get("statement_environment_hash"),
                owner_revision=node.get("revision"),
                snapshot_locator=source,
            ).to_dict()
            nodes.append(
                {
                    "ref": reference,
                    "record": node,
                    "applicability": "historical",
                }
            )
            budget.account(nodes[-1])
        helper_ids = set(helper_nodes.values())
        edges = []
        authorize_item("/dossier/proof_graph/edges")
        for index, edge in enumerate(graph.get("edges", [])):
            budget.check()
            if not isinstance(edge, dict):
                raise _Unavailable("unsupported_graph_schema")
            if not complete(edge) or _mentions_identity(
                edge, hidden_names | hidden_nodes, budget
            ):
                continue
            authorize_item(f"/dossier/proof_graph/edges/{index}")
            kind = edge.get("kind")
            meaning = (
                "inventory_member"
                if kind == "decomposes_to"
                and edge.get("source") == graph.get("root_node_id")
                and edge.get("target") in helper_ids
                else (
                    "recorded_dependency"
                    if kind in {"supports", "depends_on"}
                    else kind
                )
            )
            edges.append(
                {"record": opaque(edge), "meaning": meaning, "proof_use": "unknown"}
            )
            budget.account(edges[-1])
        session_values = {
            "lane": lane,
            "target": target,
            "context": verification,
            "helpers": helpers,
            "graph": {
                "nodes": nodes,
                "edges": edges,
                "branch_frames": selected_collection(
                    graph.get("branch_frames", []), "/dossier/proof_graph/branch_frames"
                ),
                "active_root_target_statements": selected_collection(
                    graph.get("active_root_target_statements", []),
                    "/dossier/proof_graph/active_root_target_statements",
                    allowed_mirrors=mirror_statements,
                ),
                "active_root_target_contract_identities": selected_collection(
                    graph.get("active_root_target_contract_identities", []),
                    "/dossier/proof_graph/active_root_target_contract_identities",
                    allowed_mirrors=mirror_contracts,
                ),
            },
            "research_contracts": selected_collection(
                dossier.get("research_contracts", []), "/dossier/research_contracts"
            ),
            "source_refs": source_refs,
            "coverage": {
                "selection_provenance": "only_explicit_owner_records",
                "archived_children": "not_loaded",
                "paid_response_archives": "not_loaded",
                "proof_state": "graph_records_only",
                "checker_context": "opaque",
                "proof_verification": "not_performed",
            },
        }
        # Helpers/nodes/edges were charged incrementally. Charge the remaining
        # context and contracts without serializing the complete duplicated tree.
        budget.account(
            {
                key: value
                for key, value in session_values.items()
                if key not in {"helpers", "graph"}
            }
        )
        budget.account(
            {
                key: value
                for key, value in session_values["graph"].items()
                if key not in {"nodes", "edges"}
            }
        )
        budget.check(128)
        projected.append(session_values)
    return {"sessions": projected}


def _proof(
    path: Path,
    namespace: str,
    policy: HostPolicy,
    context: AccessContext,
    budget: _Budget,
) -> tuple[dict[str, Any], dict[str, Any]]:
    raw, stamp = _read_file(path, budget)
    record = _json(raw)
    if not isinstance(record, dict):
        raise _Unavailable("unsupported_proof_schema")
    if "checkpoint_encoding" in record:
        from ..mini_session.checkpoint_pages import PageStore

        class BoundedPages(PageStore):
            @staticmethod
            def _read(directory: int, reference: Any, *, limit: int) -> bytes:
                budget.check()
                if (
                    isinstance(reference, list)
                    and len(reference) == 2
                    and isinstance(reference[0], str)
                ):
                    info = os.stat(
                        f"{reference[0]}.blob", dir_fd=directory, follow_symlinks=False
                    )
                    if info.st_nlink != 1:
                        raise _Unavailable("unsafe_source_alias")
                result = PageStore._read(directory, reference, limit=limit)
                budget.check(len(result))
                return result

        record = BoundedPages(path.parent).decode(record, limit=65536)
    # The physical envelope authenticates all decoded pages. Keep the exact
    # physical digest distinct from any owner revision or cross-source identity.
    digest = sha256_digest(raw)
    reference = _source_ref(namespace, digest, "$")
    _authorize(policy, context, reference)
    values = _proof_values(record, namespace, digest, policy, context, budget)
    if _stamp(path.stat()) != stamp:
        raise _Unavailable("source_changed")
    return values, {
        "ref": reference,
        "acquired_at": datetime.now(timezone.utc).isoformat(),
        "owner_revision": (
            record.get("sequence") if (
                _visible(record, budget)
                and _proof_value_visible(record.get("sequence"), budget, required=True)
            ) else None
        ),
        "mode": "independent_committed_copy",
    }


def _bound_research_sqlite(connection: sqlite3.Connection, budget: _Budget) -> None:
    """Apply engine limits before SQLite parses or evaluates source SQL.

    A progress callback is cooperative: it cannot interrupt every individual
    scalar operation. Exact schema admission removes source-defined expressions;
    these limits also bound individual values before they enter Python.
    """
    budget.check()
    remaining = max(1, budget.max_bytes - budget.consumed)
    limits = {
        sqlite3.SQLITE_LIMIT_LENGTH: remaining,
        sqlite3.SQLITE_LIMIT_SQL_LENGTH: min(remaining, 16384),
        sqlite3.SQLITE_LIMIT_COLUMN: 64,
        sqlite3.SQLITE_LIMIT_EXPR_DEPTH: 64,
        sqlite3.SQLITE_LIMIT_COMPOUND_SELECT: 1,
        sqlite3.SQLITE_LIMIT_VDBE_OP: 100000,
        sqlite3.SQLITE_LIMIT_FUNCTION_ARG: 16,
        sqlite3.SQLITE_LIMIT_ATTACHED: 0,
        sqlite3.SQLITE_LIMIT_VARIABLE_NUMBER: 16,
        sqlite3.SQLITE_LIMIT_TRIGGER_DEPTH: 0,
        sqlite3.SQLITE_LIMIT_WORKER_THREADS: 0,
    }
    for category, limit in limits.items():
        connection.setlimit(category, min(connection.getlimit(category), limit))


def _research_schema(connection: sqlite3.Connection, budget: _Budget) -> tuple[int, set[str]]:
    """Admit the exact owner DDL for retained versions without opening an owner."""
    from ..research_claims.store import _COLUMNS, _INDEX_SCHEMA, _SCHEMA

    budget.check()
    version = connection.execute("PRAGMA user_version").fetchone()[0]
    if (version not in _SCHEMA_VERSIONS
            or connection.execute("PRAGMA application_id").fetchone()[0] != _APPLICATION_ID):
        raise _Unavailable("unsupported_research_schema")
    tables = {
        name: fields for name, fields in _SCHEMA.items()
        if (version >= 3 or not name.startswith("discovery_"))
        and (version >= 8 or name != "frontier_records")
    }
    expected = {
        **{name: ("table", name, f"CREATE TABLE {name} ({fields})")
           for name, fields in tables.items()},
        **{name: ("index", "frontier_records" if name.startswith("frontier_") else "assignments", statement)
           for name, statement in _INDEX_SCHEMA.items()
           if version >= 8 or not name.startswith("frontier_")},
    }
    actual = {}
    for kind, name, table, definition in connection.execute(
        "SELECT type,name,tbl_name,sql FROM sqlite_master"
    ):
        budget.check()
        if name == "sqlite_sequence":
            if (kind, table, definition) != (
                "table", "sqlite_sequence", "CREATE TABLE sqlite_sequence(name,seq)"
            ):
                raise _Unavailable("unsupported_research_schema")
        elif name.startswith("sqlite_autoindex_"):
            if (kind != "index" or table not in tables or definition is not None
                    or name != f"sqlite_autoindex_{table}_1"):
                raise _Unavailable("unsupported_research_schema")
        else:
            actual[name] = (kind, table, definition)
    if actual != expected:
        raise _Unavailable("unsupported_research_schema")
    for table in tables:
        budget.check()
        columns = list(connection.execute(f"PRAGMA table_xinfo({table})"))
        if ([row[1] for row in columns] != _COLUMNS[table]
                or any(row[6] != 0 for row in columns)):
            raise _Unavailable("unsupported_research_schema")
    return version, set(tables)


def _research_json(data: bytes | str, budget: _Budget) -> Any:
    """Check input size before decoding; retained records are charged separately."""
    budget.check()
    remaining = budget.max_bytes - budget.consumed
    if not isinstance(data, (bytes, str)) or len(data) > remaining:
        raise _Unavailable("byte_limit_exceeded")
    if isinstance(data, str):
        size = 0
        for offset in range(0, len(data), 4096):
            budget.check()
            size += len(data[offset : offset + 4096].encode("utf-8"))
            if size > remaining:
                raise _Unavailable("byte_limit_exceeded")
    result = _json(data)
    budget.check()
    return result


def _frontier_dependencies(record: dict[str, Any], kind: str, budget: _Budget) -> dict[str, Any]:
    """Select owner-defined campaign references, excluding prose and backrefs."""
    budget.check()
    fields = {
        "routes": ("approach_id", "bottleneck", "root_obligation", "reductions"),
        "approaches": ("route_id", "question_id", "bottleneck_obligation", "parent_id"),
        "questions": ("approach_id", "route_id", "previous_question_id"),
        "reductions": ("antecedents", "consequent", "route_id"),
        "evidence_events": ("operation_id", "group"),
        "entitlements": ("event_id", "group", "permit_id"),
        "permits": ("approach_id", "question_id", "route_id", "entitlement_id", "claim_id", "provenance_entitlement"),
        "claims": ("permit_id",), "source_applications": ("question_id",),
        "experiments": ("question_id", "observation_id"),
        "review_authorizations": ("question_id",), "proof_handoffs": ("approach_id",),
        "decisions": ("approach_id", "obligation_id", "event_id", "entitlement_id", "permit_id"),
        "scoped_holds": ("obligation_id", "approach_id"),
        "tool_operations": ("observation_id",), "observations": ("cost",),
    }
    result = {key: record[key] for key in fields.get(kind, ()) if key in record}
    if kind in {"observations", "tool_operations"} and isinstance(record.get("binding"), dict):
        binding = record["binding"]
        result["binding"] = {key: binding[key] for key in (
            "approach_id", "question_id", "route_id", "control_authorization") if key in binding}
    if kind == "research_findings" and isinstance(record.get("assessment"), dict):
        result["assessment"] = _frontier_dependencies(record["assessment"], "decisions", budget)
        if "decision_id" in record["assessment"]:
            result["assessment"]["decision_id"] = record["assessment"]["decision_id"]
    return result


def _frontier_reference_paths(kind: str) -> dict[tuple[Any, ...], str | tuple[str, ...]]:
    direct = {
        "routes": {"approach_id": "approaches", "bottleneck": "obligations", "root_obligation": "obligations"},
        "approaches": {"route_id": "routes", "question_id": "questions", "bottleneck_obligation": "obligations",
                       "parent_id": "approaches"},
        "questions": {"approach_id": "approaches", "route_id": "routes", "previous_question_id": "questions"},
        "reductions": {"consequent": "obligations", "route_id": "routes"},
        "evidence_events": {"group": "evidence_events"},
        "entitlements": {"event_id": "evidence_events", "group": "evidence_events", "permit_id": "permits"},
        "permits": {"approach_id": "approaches", "question_id": "questions", "route_id": "routes",
                    "entitlement_id": "entitlements", "claim_id": "claims", "provenance_entitlement": "entitlements"},
        "claims": {"permit_id": "permits"}, "source_applications": {"question_id": "questions"},
        "experiments": {"question_id": "questions", "observation_id": "observations"},
        "review_authorizations": {"question_id": "questions"}, "proof_handoffs": {"approach_id": "approaches"},
        "decisions": {"approach_id": "approaches", "obligation_id": "obligations", "event_id": "evidence_events",
                      "entitlement_id": "entitlements", "permit_id": "permits"},
        "scoped_holds": {"obligation_id": "obligations", "approach_id": "approaches"},
        "tool_operations": {"observation_id": "observations"},
        "jobs": {"frontier_approach_id": "approaches", "frontier_question_id": "questions",
                 "frontier_claim_id": "claims", "frontier_last_observation": "observations",
                 "frontier_review_authorization": "review_authorizations", "frontier_refused_permit_id": "permits"},
        "subjects": {"question_id": "questions"},
    }
    paths: dict[tuple[Any, ...], str | tuple[str, ...]] = {(key,): domain for key, domain in direct.get(kind, {}).items()}
    if kind == "routes":
        paths[("reductions", _LIST_ITEM)] = "reductions"
    if kind == "reductions":
        paths[("antecedents", _LIST_ITEM)] = "obligations"
    if kind == "evidence_events":
        paths[("operation_id",)] = ("operations", "tool_operations")
    if kind == "observations":
        paths[("cost", _LIST_ITEM)] = ("operations", "tool_operations")
    binding = {"approach_id": "approaches", "question_id": "questions", "route_id": "routes",
               "control_authorization": "review_authorizations"}
    if kind in {"observations", "tool_operations", "subjects"}:
        paths.update({("binding", key): domain for key, domain in binding.items()})
    if kind == "jobs":
        for prefix in (("frontier_report_basis", "binding"), ("frontier_consumed_basis",)):
            paths.update({prefix + (key,): domain for key, domain in binding.items()})
    if kind == "research_findings":
        paths.update({("assessment",) + path: domain for path, domain in _frontier_reference_paths("decisions").items()})
        paths[("assessment", "decision_id")] = "decisions"
    return paths


def _frontier_external_fields(kind: str) -> tuple[str, ...]:
    return {
        # Operation IDs can name different owner kinds. Authorization producer
        # and basis references use the supported owner-domain unions below.
        "evidence_events": ("operation_id", "artifacts", "checked_basis"),
        "reductions": ("certificate",),
        "review_authorizations": ("evidence_basis", "producer_ids"),
        "research_findings": ("reviewer_id", "producer_id", "target_claim_id", "report_artifact",
                              "baseline_artifact_ids", "prior_report_artifact_ids", "comparison_scope_artifact"),
        "proof_handoffs": ("producer_id", "consumer_id"),
        "tool_operations": ("job_id", "response_artifact", "input_artifact", "result_artifact"),
        "observations": ("artifacts",),
    }.get(kind, ())


def _frontier_external_dependencies(record: dict[str, Any], kind: str, budget: _Budget) -> dict[str, Any]:
    """References leaving a campaign, separate from its local identity names."""
    budget.check()
    result = {key: record[key] for key in _frontier_external_fields(kind) if key in record}
    binding = record.get("binding")
    if kind in {"observations", "tool_operations"} and isinstance(binding, dict):
        result["binding"] = {key: binding[key] for key in ("native_target_claim_id",) if key in binding}
    return result


@dataclass
class _FrontierDefinition:
    identity: str
    kind: str
    identities: set[tuple[str, str]]
    local: dict[str, Any]
    external: dict[str, Any]
    indexed: bool


def _frontier_definition_fields() -> dict[str, str]:
    return {
        "routes": "route_id", "approaches": "approach_id", "questions": "question_id",
        "obligations": "obligation_id", "reductions": "reduction_id",
        "evidence_events": "event_id", "entitlements": "entitlement_id",
        "permits": "permit_id", "claims": "claim_id", "observations": "observation_id",
        "source_applications": "application_id", "experiments": "experiment_id",
        "review_authorizations": "authorization_id", "research_findings": "finding_id",
        "proof_handoffs": "handoff_id", "tool_operations": "operation_id",
    }


def _frontier_decision_identity(record: Any, budget: _Budget) -> str | None:
    """Recognize the full owner decision shape, rather than an ID-only reference."""
    budget.check()
    if not isinstance(record, dict):
        return None
    identity = record.get("decision_id")
    if not isinstance(identity, str) or not identity:
        return None
    for field in (
        "approach_id", "obligation_id", "event_id", "created", "evidence_class",
        "certificate_retained", "entitlement_id", "permit_id", "explanation", "credit_minted",
    ):
        budget.check()
        if field not in record:
            return None
    return identity


def _hidden_research_identities(
    table: str, value: Any, budget: _Budget, *, kind: str = ""
) -> tuple[set[str], set[tuple[str, str]], dict[str, set[str]], list[_FrontierDefinition]]:
    """Collect hidden definitions at owner-declared containment locations.

    A table row owns its primary ID, already collected by the caller. Its other
    IDs usually reference public prerequisites: a job's claim/evidence, a
    subject's producer/question, or a frontier route's approach. Nested IDs may
    also be local labels, such as ClaimSpec obligation names, whose references
    require their enclosing claim. Frontier definitions are resolved within
    their campaign; only its independently indexed rows have global IDs.
    Arbitrary metadata and dictionary keys cannot establish aliases.
    """
    budget.check()
    hidden: set[tuple[str, str]] = set()
    references: dict[str, set[str]] = {}
    definitions: list[_FrontierDefinition] = []
    if table != "frontier_records" or kind != "campaign" or not isinstance(value, dict):
        return set(), hidden, references, definitions

    def collect(record: Any, identity: Any, field: str, collection: str, *, global_id: bool = False) -> None:
        budget.check()
        if isinstance(identity, str) and identity and isinstance(record, dict):
            budget.check(128)
            budget.account(identity)
            dependencies = _frontier_dependencies(record, collection, budget)
            external = _frontier_external_dependencies(record, collection, budget)
            budget.account(dependencies)
            budget.account(external)
            definitions.append(_FrontierDefinition(identity, collection, {(collection, identity)}, dependencies, external, global_id))
            references.setdefault(field, set()).add(identity)
            if _contains_hidden(record, budget):
                hidden.add((collection, identity))

    def sequence(container: Any, field: str, collection: str, *, global_id: bool = False) -> None:
        budget.check()
        if isinstance(container, list):
            for record in container:
                budget.check()
                if isinstance(record, dict):
                    collect(record, record.get(field), field, collection, global_id=global_id)

    # These collections define entities in the frontier owner, including those
    # kept only in the campaign. Caller-supplied obligation names remain local.
    for collection, field in _frontier_definition_fields().items():
        budget.check()
        records = value.get(collection)
        if isinstance(records, dict):
            for record in records.values():
                budget.check()
                if isinstance(record, dict):
                    collect(record, record.get(field), field, collection,
                            global_id=collection in {"routes", "approaches", "questions"})
    sequence(value.get("decisions"), "decision_id", "decisions", global_id=True)
    # assess_delta stores the full apply_contribution result under its finding.
    # Persistence splits that object from the decisions-list/indexed copy. Its
    # primary identity survives independent annotations or body edits; a hidden
    # finding wrapper alone does not change the decision's visibility.
    decisions, findings = value.get("decisions"), value.get("research_findings")
    if isinstance(decisions, list) and isinstance(findings, dict):
        decision_ids = set()
        for decision in decisions:
            identity = _frontier_decision_identity(decision, budget)
            if identity is not None:
                budget.check(128)
                budget.account(identity)
                decision_ids.add(identity)
        for finding in findings.values():
            budget.check()
            assessment = finding.get("assessment") if isinstance(finding, dict) else None
            identity = _frontier_decision_identity(assessment, budget)
            if identity is not None and identity in decision_ids:
                collect(assessment, identity, "decision_id", "decisions", global_id=True)
    sequence(value.get("scoped_holds"), "hold_id", "scoped_holds")
    # retry.authorize_execution defines operation IDs only as keys in this
    # exact map; persist._projection_rows uses those keys as row identities.
    operations = value.get("operations")
    if isinstance(operations, dict):
        for identity, record in operations.items():
            collect(record, identity, "operation_id", "operations", global_id=True)
    # The tool owner records an experiment execution under its tool operation
    # identity. Only this explicit coindexed shape establishes a cross-kind alias.
    tool_operations, experiments = value.get("tool_operations"), value.get("experiments")
    if isinstance(tool_operations, dict) and tool_operations and isinstance(experiments, dict) and experiments:
        by_identity = {}
        for definition in definitions:
            budget.check()
            if definition.kind in {"tool_operations", "experiments"}:
                budget.check(128)
                by_identity[(definition.kind, definition.identity)] = definition
        for identity, operation in tool_operations.items():
            budget.check()
            experiment = experiments.get(identity)
            if (isinstance(operation, dict) and operation.get("action") == "experiment"
                    and operation.get("operation_id") == identity
                    and isinstance(experiment, dict) and experiment.get("experiment_id") == identity):
                aliases = {("tool_operations", identity), ("experiments", identity)}
                budget.check(256)
                for key in aliases:
                    if key in by_identity:
                        by_identity[key].identities.update(aliases)
    # Definitions remain available even if their containing campaign row is
    # omitted. The outer closure resolves both local and external prerequisites.
    return {definition.identity for definition in definitions
            if definition.indexed and definition.identities & hidden}, hidden, references, definitions


def _frontier_scope(
    candidate: _ResearchRecord, owners: dict[tuple[str, str], set[str]], budget: _Budget
) -> tuple[set[str], Any, str]:
    """Resolve campaign scope only through canonical owner references."""
    budget.check()
    record = candidate.value["record"]
    if candidate.table == "frontier_records":
        kind = {"route": "routes", "approach": "approaches", "question": "questions",
                "contribution": "decisions", "operation": "operations"}.get(record["kind"], "")
        return {record["owner_id"]}, _frontier_dependencies(record["record"], kind, budget), kind
    references: list[tuple[str, Any]] = []
    values: dict[str, Any] = {}
    kind = ""
    body: Any = {}
    if candidate.table == "discovery_jobs" and isinstance(record.get("record"), dict):
        body = record["record"]
        kind = "jobs"
    elif candidate.table == "subjects":
        body = record
        kind = "subjects"
    # The same canonical paths govern scope inference and typed matching,
    # including nested report/consumption bindings without top-level anchors.
    owner_fields = {"approaches": "approach_id", "questions": "question_id", "routes": "route_id",
                    "review_authorizations": "authorization_id", "claims": "claim_id",
                    "permits": "permit_id", "observations": "observation_id"}
    for path, domain in _frontier_reference_paths(kind).items():
        budget.check()
        value = body
        for key in path:
            budget.check()
            if not isinstance(value, dict) or key not in value:
                break
            value = value[key]
        else:
            selected = values
            for key in path[:-1]:
                selected = selected.setdefault(key, {})
            selected[path[-1]] = value
            if isinstance(domain, str) and domain in owner_fields:
                references.append((owner_fields[domain], value))
    scopes: set[str] | None = None
    candidates: set[str] = set()
    for field, reference in references:
        budget.check()
        known = owners.get((field, reference)) if isinstance(reference, str) else None
        if known:
            candidates.update(known)
            scopes = set(known) if scopes is None else scopes & known
    # Compatible references narrow scope precisely. Conflicting references do
    # not erase known restrictions: inspect their possible owners and omit only
    # this candidate if any required identity is hidden there.
    return (scopes if scopes else candidates), values, kind


@dataclass
class _ResearchRecord:
    table: str
    identity: str
    value: dict[str, Any]
    identities: set[tuple[str, str]]


def _research_reference_paths(table: str, kind: str) -> dict[tuple[Any, ...], str | tuple[str, ...]]:
    """Type only canonical owner locations; arbitrary metadata stays opaque."""
    paths: dict[tuple[Any, ...], str | tuple[str, ...]] = {}
    if table in _TABLES:
        primary = _TABLES[table][0]
        paths[(primary,)] = table
        paths[("spec" if table == "revisions" else "record", primary)] = table
    if table in {"revisions", "evidence", "reviews", "contributions", "operations"}:
        paths[("claim_id",)] = "revisions"
        paths[("spec" if table == "revisions" else "record", "claim_id")] = "revisions"
    fields: dict[str, str] = {}
    if table == "revisions":
        paths[("spec", "dependencies", _LIST_ITEM, "supplier_id")] = "revisions"
        paths[("spec", "dependencies", _LIST_ITEM, "obligation_id")] = "claim_obligations"
        paths[("spec", "supersedes", _LIST_ITEM)] = "revisions"
    elif table == "discovery_jobs":
        fields = {"claim_id": "revisions", "evidence_id": "evidence",
                  "native_target_claim_id": "revisions", "frontier_native_target_claim_id": "revisions",
                  "parent_job": "discovery_jobs", "research_reorientation_for": "discovery_jobs",
                  "assigned_research_subject": "artifacts",
                  "frontier_approach_id": "frontier_records", "frontier_question_id": "frontier_records"}
        paths[("record", "supersedes_review_ids", _LIST_ITEM)] = "reviews"
    elif table == "evidence":
        paths[("record", "artifact_ids", _LIST_ITEM)] = "artifacts"
    elif table == "reviews":
        fields = {"evidence_id": "evidence"}
        paths[("record", "supersedes_review_ids", _LIST_ITEM)] = "reviews"
    elif table == "contributions":
        fields = {"supplier_id": "revisions"}
        paths[("record", "supersedes_contribution_ids", _LIST_ITEM)] = "contributions"
    elif table == "frontier_records":
        paths[("target_id",)] = "revisions"
        frontier_primary = {"approach": "approach_id", "route": "route_id", "question": "question_id",
                   "contribution": "decision_id"}.get(kind)
        fields = {key: "frontier_records" for key in {
            "approach": ("approach_id", "route_id", "question_id"),
            "route": ("route_id", "approach_id"), "question": ("question_id", "approach_id"),
            "contribution": ("decision_id", "approach_id"),
        }.get(kind, ())}
        if frontier_primary:
            fields[frontier_primary] = "frontier_records"
    elif table == "subjects":
        paths.update({(key,): domain for key, domain in {
            "subject_id": "subjects", "producer_job_id": "discovery_jobs", "reviewer_job_id": "discovery_jobs",
            "checkpoint_artifact": "artifacts", "report_artifact": "artifacts",
            "native_checkpoint_artifact": "artifacts", "question_id": "frontier_records",
        }.items()})
        paths.update({("binding", key): "frontier_records" for key in ("approach_id", "question_id", "route_id")})
    elif table == "frontier_dependencies":
        paths.update({(key,): "discovery_jobs" for key in ("job_id", "producer_id", "reviewer_id", "consumer_id")})
        # hooks creates producers from jobs or research authors, and bases from
        # jobs, ledger evidence or strategy reviews. None identifies a claim.
        paths[("producer_ids", _LIST_ITEM)] = ("discovery_jobs", "research_authors")
        paths[("evidence_basis",)] = ("discovery_jobs", "evidence", "strategy_reviews")
        paths[("certificate",)] = "discovery_jobs"
        paths[("target_claim_id",)] = "revisions"
        paths[("binding", "native_target_claim_id")] = "revisions"
        paths.update({(key,): "artifacts" for key in (
            "report_artifact", "comparison_scope_artifact", "response_artifact", "input_artifact", "result_artifact")})
        paths.update({(key, _LIST_ITEM): "artifacts" for key in (
            "artifacts", "baseline_artifact_ids", "prior_report_artifact_ids")})
    paths.update({("record", key): domain for key, domain in fields.items()})
    local_kind = {"approach": "approaches", "route": "routes", "question": "questions",
                  "contribution": "decisions", "operation": "operations"}.get(kind, "")
    if table in {"discovery_jobs", "subjects"}:
        local_kind = "jobs" if table == "discovery_jobs" else "subjects"
    if table in {"frontier_records", "discovery_jobs", "subjects"}:
        prefix = () if table == "subjects" else ("record",)
        for path, domain in _frontier_reference_paths(local_kind).items():
            if isinstance(domain, str):
                paths[prefix + path] = "frontier_records" if domain in {
                    "routes", "approaches", "questions", "decisions", "operations"} else "frontier_local"
        binding_prefixes = (("binding",),) if table == "subjects" else (
            ("record", "frontier_report_basis", "binding"), ("record", "frontier_consumed_basis"))
        if table in {"discovery_jobs", "subjects"}:
            for binding_prefix in binding_prefixes:
                paths[binding_prefix + ("native_target_claim_id",)] = "revisions"
                for key in ("root_binding", "native_context_binding"):
                    paths[binding_prefix + (key,)] = "frontier_context"
        if table == "discovery_jobs":
            paths[("record", "frontier_report_basis", "attempt_id")] = "strategy_attempts"
            for key in ("response_artifact", "report_artifact"):
                paths[("record", "frontier_report_basis", key)] = "artifacts"
    return paths


def _mentions_typed_identity(
    record: Any, hidden: set[tuple[str, str]], tokens: set[str],
    paths: dict[tuple[Any, ...], str | tuple[str, ...]], budget: _Budget,
    maps: dict[tuple[Any, ...], tuple[str, str | None]] | None = None,
) -> bool:
    prefixes = {path[:length] for path in paths for length in range(1, len(path) + 1)}

    def visit(value: Any, path: tuple[Any, ...]) -> bool:
        budget.check()
        if not _visible(value, budget):
            return False
        if isinstance(value, str):
            domain = paths.get(path)
            if isinstance(domain, tuple):
                return any((item, value) in hidden for item in domain)
            return (domain, value) in hidden if domain else value in tokens
        if isinstance(value, dict):
            mapping = (maps or {}).get(path)
            for key, item in value.items():
                budget.check()
                if key.lower() in _HIDDEN_FIELDS:
                    continue
                child_path = path + (key,)
                if (mapping is not None and isinstance(item, dict)
                        and (mapping[1] is None or item.get(mapping[1]) == key)):
                    # Only declared owner maps with a matching record identity
                    # type their keys; arbitrary or inconsistent maps stay generic.
                    child_path = path + (_MAP_VALUE,)
                    key_hidden = (mapping[0], key) in hidden
                else:
                    key_hidden = key in tokens and child_path not in prefixes
                if key_hidden or visit(item, child_path):
                    return True
            return False
        if isinstance(value, list):
            return any(visit(item, path + (_LIST_ITEM,)) for item in value)
        return False

    return visit(record, ())


def _campaign_reference_paths(
    paths: dict[tuple[Any, ...], str | tuple[str, ...]], budget: _Budget,
) -> dict[tuple[Any, ...], tuple[str, str | None]]:
    """Apply the same typed definitions and references to the campaign copy."""
    maps: dict[tuple[Any, ...], tuple[str, str | None]] = {}
    indexed = {"routes", "approaches", "questions", "decisions", "operations"}
    external = _research_reference_paths("frontier_dependencies", "")
    definitions: dict[str, str | None] = {
        **_frontier_definition_fields(), "decisions": "decision_id", "scoped_holds": "hold_id", "operations": None,
    }
    for collection, primary in definitions.items():
        budget.check()
        domain = "frontier_records" if collection in indexed else "frontier_local"
        container = ("record", collection)
        prefix = container + ((_LIST_ITEM,) if collection in {"decisions", "scoped_holds"} else (_MAP_VALUE,))
        if collection not in {"decisions", "scoped_holds"}:
            maps[container] = (domain, primary)
        if primary:
            paths[prefix + (primary,)] = domain
        for path, reference_domain in _frontier_reference_paths(collection).items():
            budget.check()
            if isinstance(reference_domain, str):
                paths[prefix + path] = "frontier_records" if reference_domain in indexed else "frontier_local"
        fields = _frontier_external_fields(collection)
        for path, reference_domain in external.items():
            budget.check()
            if path[0] in fields or (path[0] == "binding" and collection in {"observations", "tool_operations"}):
                paths[prefix + path] = reference_domain
    paths[("record", "root", "target_id")] = "revisions"
    paths[("record", "native_active_target_claim_id")] = "revisions"
    paths[("record", "root_obligation")] = "frontier_local"
    return maps


def _mentions_research_identity(
    candidate: _ResearchRecord, hidden: set[tuple[str, str]], tokens: set[str], budget: _Budget
) -> bool:
    record = candidate.value["record"]
    paths = _research_reference_paths(candidate.table, record.get("kind", ""))
    if candidate.table in _TABLES:
        body_key = "spec" if candidate.table == "revisions" else "record"
        primary = _TABLES[candidate.table][0]
        if candidate.table == "frontier_records":
            primary = {"approach": "approach_id", "route": "route_id", "question": "question_id",
                       "contribution": "decision_id"}.get(record.get("kind", ""), primary)
        body = record.get(body_key)
        if isinstance(body, dict) and body.get(primary) != candidate.identity:
            # A malformed duplicate primary field cannot claim a typed exemption.
            paths.pop((body_key, primary), None)
    maps = _campaign_reference_paths(paths, budget) if (
        candidate.table == "frontier_records" and record.get("kind") == "campaign") else None
    return _mentions_typed_identity(record, hidden, tokens, paths, budget, maps)


def _mentions_frontier_identity(
    record: Any, kind: str, hidden: set[tuple[str, str]], budget: _Budget
) -> bool:
    tokens = set()
    for _, identity in hidden:
        budget.check()
        tokens.add(identity)
    return _mentions_typed_identity(record, hidden, tokens, _frontier_reference_paths(kind), budget)


def _research_records(
    connection: sqlite3.Connection,
    tables: set[str],
    namespace: str,
    digest: str,
    policy: HostPolicy,
    context: AccessContext,
    budget: _Budget,
) -> tuple[list[_ResearchRecord], dict[str, str]]:
    """Resolve visibility before publishing any record or dependent relationship."""
    records: list[_ResearchRecord] = []
    hidden: set[tuple[str, str]] = set()
    hidden_tokens: set[str] = set()
    hidden_by_campaign: dict[str, set[tuple[str, str]]] = {}
    campaign_definitions: dict[str, list[_FrontierDefinition]] = {}
    frontier_owners: dict[tuple[str, str], set[str]] = {}
    assigned_subjects: dict[str, str] = {}
    missing_subjects: dict[str, str] = {}
    for table, columns in _TABLES.items():
        budget.check(128)
        if table not in tables:
            continue
        for row in connection.execute(f"SELECT {','.join(columns)} FROM {table} ORDER BY 1,2"):
            budget.check()
            item = dict(row)
            for key in ("record", "spec"):
                if key in item:
                    item[key] = _research_json(item[key], budget)
            identity = str(row[0])
            if table == "frontier_records":
                budget.account([identity, item["owner_id"]])
                field = {"approach": "approach_id", "question": "question_id", "route": "route_id"}.get(item["kind"])
                if field:
                    frontier_owners.setdefault((field, identity), set()).add(item["owner_id"])
            source = _source_ref(namespace, digest, f"{table}/{identity}/{item.get('revision', '')}")
            authorized = policy.authorize(source, context)
            body = item.get("record", item.get("spec", item))
            indexed, scoped, references, definitions = _hidden_research_identities(
                table, body, budget, kind=item.get("kind", ""))
            hidden.update(("frontier_records", identity) for identity in indexed)
            hidden_tokens.update(indexed)
            if scoped:
                hidden_by_campaign.setdefault(item["owner_id"], set()).update(scoped)
            if definitions:
                campaign_definitions.setdefault(item["owner_id"], []).extend(definitions)
            for field, identities in references.items():
                for reference in identities:
                    budget.account([field, reference, item["owner_id"]])
                    frontier_owners.setdefault((field, reference), set()).add(item["owner_id"])
            if table == "discovery_jobs" and isinstance(body, dict):
                subject_id = body.get("assigned_research_subject")
                if subject_id:
                    if not isinstance(subject_id, str):
                        raise _Unavailable("unsupported_subject_reference")
                    # Omitted jobs can still identify hidden subjects whose
                    # alternate identities appear in other retained records.
                    budget.account([identity, subject_id])
                    assigned_subjects[identity] = subject_id
                elif body.get("research_reorientation_for"):
                    budget.account(identity)
                    missing_subjects[identity] = identity
            if not authorized or _contains_hidden(body, budget):
                hidden.add((table, identity))
                hidden_tokens.add(identity)
                budget.account(identity)
                continue
            projected = {"source_ref": source, "record": _opaque(item, budget),
                         "applicability": "historical"}
            budget.account(projected)
            records.append(_ResearchRecord(table, identity, projected, {(table, identity)}))

    # Resolve identities privately even for denied subjects and omitted jobs.
    # These identities are needed to omit dependent records, never to expose
    # the denied artifact's content. No partial job escapes first.
    subjects: dict[str, _ResearchRecord | None] = {}
    for job_id, subject_id in assigned_subjects.items():
        budget.check()
        if subject_id in subjects:
            if subjects[subject_id] is None and ("artifacts", subject_id) not in hidden:
                missing_subjects[job_id] = job_id
            continue
        source = _source_ref(namespace, digest, f"artifacts/{subject_id}")
        subjects[subject_id] = None
        authorized = policy.authorize(source, context)
        if not authorized:
            hidden.add(("artifacts", subject_id))
            hidden_tokens.add(subject_id)
            budget.account(subject_id)
        row = connection.execute("SELECT content FROM artifacts WHERE artifact_id=?", (subject_id,)).fetchone()
        if row is None:
            if authorized:
                missing_subjects[job_id] = job_id
            continue
        budget.check()
        if not isinstance(row[0], bytes) or sha256_digest(row[0]) != subject_id:
            raise _Unavailable("artifact_integrity_failure")
        subject = _research_json(row[0], budget)
        subject_identities = {("artifacts", subject_id)}
        if isinstance(subject, dict) and isinstance(subject.get("subject_id"), str):
            subject_identities.add(("subjects", subject["subject_id"]))
        if not authorized or _contains_hidden(subject, budget):
            hidden.update(subject_identities)
            hidden_tokens.update(identity for _, identity in subject_identities)
            budget.account([list(identity) for identity in subject_identities])
            continue
        projected = {"source_ref": source, "record": _opaque(subject, budget)}
        budget.account(projected)
        candidate_subject = _ResearchRecord("subjects", subject_id, projected, subject_identities)
        subjects[subject_id] = candidate_subject
        records.append(candidate_subject)

    # IDs are matched as complete values/keys, never substrings in prose. Close
    # transitively across tables and subjects, keeping conclusions with all of
    # their premises or omitting the complete record.
    while True:
        kept = []
        changed = False
        for owner, definitions in campaign_definitions.items():
            scoped = hidden_by_campaign.setdefault(owner, set())
            for definition in definitions:
                budget.check()
                identity = definition.identity
                external = _ResearchRecord("frontier_dependencies", identity, {"record": definition.external}, set())
                if not definition.identities <= scoped and (
                    definition.identities & scoped
                    or (definition.indexed and ("frontier_records", identity) in hidden)
                    or _mentions_frontier_identity(definition.local, definition.kind, scoped, budget)
                    or _mentions_research_identity(external, hidden, hidden_tokens, budget)
                ):
                    scoped.update(definition.identities)
                    changed = True
                if definition.indexed and definition.identities & scoped:
                    hidden.add(("frontier_records", identity))
                    hidden_tokens.add(identity)
        for candidate in records:
            budget.check()
            owners, scoped_record, scoped_kind = _frontier_scope(candidate, frontier_owners, budget)
            if (candidate.identities & hidden
                    or _mentions_research_identity(candidate, hidden, hidden_tokens, budget)
                    or any(_mentions_frontier_identity(scoped_record, scoped_kind, hidden_by_campaign.get(owner, set()), budget)
                           for owner in owners)):
                hidden.update(candidate.identities)
                hidden_tokens.update(identity for _, identity in candidate.identities)
                changed = True
            else:
                kept.append(candidate)
        records = kept
        if not changed:
            break
    retained_jobs = {candidate.identity: candidate.value["record"]["record"]
                     for candidate in records if candidate.table == "discovery_jobs"}
    retained_subjects = {job.get("assigned_research_subject") for job in retained_jobs.values()
                         if isinstance(job, dict) and isinstance(job.get("assigned_research_subject"), str)}
    records = [candidate for candidate in records
               if candidate.table != "subjects" or candidate.identity in retained_subjects]
    return records, {key: value for key, value in missing_subjects.items() if key in retained_jobs}


def _research(
    path: Path,
    namespace: str,
    policy: HostPolicy,
    context: AccessContext,
    budget: _Budget,
) -> tuple[dict[str, Any], dict[str, Any]]:
    if path.is_dir():
        path = path / "ledger.sqlite3"
    sidefiles = [Path(str(path) + suffix) for suffix in ("-wal", "-shm", "-journal")]
    if any(item.exists() or item.is_symlink() for item in sidefiles):
        raise _Unavailable("unsafe_live_source")
    raw, stamp = _read_file(path, budget)
    if not raw.startswith(b"SQLite format 3\x00") or len(raw) < 100:
        raise _Unavailable("unsupported_research_schema")
    digest = sha256_digest(raw)
    reference = _source_ref(namespace, digest, "$")
    _authorize(policy, context, reference)
    # Deserialize the authenticated independent copy into private memory. A
    # clean WAL-mode export retains WAL header flags even with no WAL frames;
    # memory databases need rollback flags. Only these two private bytes change.
    memory_image = raw[:18] + b"\x01\x01" + raw[20:]
    budget.check(1024)
    values: dict[str, Any] = {"claims": [], "questions": [], "subjects": []}
    connection = sqlite3.connect(":memory:", isolation_level=None)
    try:
        _bound_research_sqlite(connection, budget)
        connection.deserialize(memory_image)
        connection.row_factory = sqlite3.Row
        connection.set_progress_handler(
            lambda: int(time.monotonic() >= budget.deadline), 1000
        )
        connection.execute("PRAGMA query_only = ON")
        connection.execute("PRAGMA trusted_schema = OFF")
        connection.execute("BEGIN")
        version, tables = _research_schema(connection, budget)
        heads = {}
        for row in connection.execute("SELECT claim_id, revision FROM claims"):
            budget.check()
            heads[row[0]] = row[1]
        records, missing = _research_records(
            connection, tables, namespace, digest, policy, context, budget
        )
        values.update({table: [] for table in _TABLES})
        for candidate in records:
            budget.check()
            projected = candidate.value
            item = projected["record"]
            if candidate.table == "revisions" and heads.get(item["claim_id"]) == item["revision"]:
                budget.account(projected)
                values["claims"].append(projected)
            if candidate.table == "frontier_records" and item["kind"] == "question":
                projected["ref"] = QuestionRef(
                    namespace=namespace, ledger=namespace,
                    question_id=item["record_id"], formulation_revision=item["revision"],
                ).to_dict()
                budget.account(projected)
                values["questions"].append(projected)
            values[candidate.table].append(projected)
        missing_subjects = list(missing.values())
        budget.account(missing_subjects)
        values["coverage"] = {
            "missing_subjects": missing_subjects,
            "artifact_bodies": "assigned_subjects_only",
            "event_history": "not_loaded",
            "source_schema_version": version,
        }
        budget.account(values["coverage"])
        connection.execute("ROLLBACK")
    finally:
        connection.close()
    if _stamp(path.stat()) != stamp or any(item.exists() for item in sidefiles):
        raise _Unavailable("source_changed")
    return values, {
        "ref": reference,
        "acquired_at": datetime.now(timezone.utc).isoformat(),
        "owner_revision": None,
        "mode": "independent_committed_copy",
    }


def read_owner_inputs(
    *,
    proof_path: str | Path | None = None,
    research_path: str | Path | None = None,
    proof_source_id: str = "proof",
    research_source_id: str = "research",
    policy: HostPolicy,
    context: AccessContext,
    offline: bool = False,
    max_bytes: int = 64 * 1024 * 1024,
    timeout_seconds: float = 10.0,
) -> dict[str, Any]:
    """Return copied authorized values with explicit, separately acquired coverage.

    Missing, unsafe, changed or oversized components are discarded in full.
    Authorization failures reveal neither file existence nor record counts.
    Caller-selected ``source_id`` values are stable host policy namespaces.
    """
    if offline is not True:
        raise ProjectionError(
            "source_unavailable", "only independent committed copies are supported"
        )
    context_binding(context)
    if (
        type(max_bytes) is not int
        or max_bytes < 1
        or not isinstance(timeout_seconds, (int, float))
        or isinstance(timeout_seconds, bool)
        or not math.isfinite(timeout_seconds)
        or timeout_seconds <= 0
    ):
        raise ValueError("positive byte and deadline limits are required")
    selected = [
        ("proof", proof_path, proof_source_id, _proof),
        ("research", research_path, research_source_id, _research),
    ]
    dependencies: list[dict[str, Any]] = []
    # Authorize every selected namespace before touching any selected source.
    for _, path, namespace, _ in selected:
        if path is not None:
            if not isinstance(namespace, str) or not namespace:
                raise ValueError("source namespaces must be nonempty strings")
            dependency = {
                "kind": "source",
                "version": 1,
                "namespace": namespace,
                "item": "*",
            }
            _authorize(policy, context, dependency)
            dependencies.append(dependency)
    budget = _Budget(max_bytes=max_bytes, deadline=time.monotonic() + timeout_seconds)
    values: dict[str, Any] = {}
    sources: dict[str, Any] = {}
    coverage: dict[str, Any] = {}
    for kind, path, namespace, reader in selected:
        if path is None:
            coverage[kind] = {"status": "missing", "reason": "not_selected"}
            continue
        try:
            component, source = reader(Path(path), namespace, policy, context, budget)
            component_dependencies = {}
            pending = [component, source["ref"]]
            while pending:
                budget.check()
                current = pending.pop()
                if isinstance(current, dict):
                    if current.get("kind") == "source" and current.get("version") == 1:
                        key = canonical_json(current)
                        budget.check()
                        if key not in component_dependencies:
                            budget.check(len(key))
                            component_dependencies[key] = current
                    pending.extend(current.values())
                elif isinstance(current, list):
                    pending.extend(current)
            budget.check()
            values[kind], sources[kind] = component, source
            coverage[kind] = {"status": "observed"}
            dependencies.extend(component_dependencies.values())
        except FileNotFoundError:
            coverage[kind] = {"status": "missing", "reason": "source_missing"}
        except ProjectionError:
            raise
        except _Unavailable as error:
            coverage[kind] = {"status": "source_unavailable", "reason": str(error)}
        except (
            OSError,
            ValueError,
            TypeError,
            KeyError,
            AttributeError,
            RecursionError,
            sqlite3.Error,
        ):
            coverage[kind] = {
                "status": "source_unavailable",
                "reason": "invalid_or_unreadable_source",
            }
    coverage["selected_sources_observed"] = all(
        coverage[kind]["status"] == "observed" for kind in ("proof", "research")
    )
    coverage["complete"] = False
    coverage["scope"] = "retained_supported_records"
    # Each accepted component already retained its exact per-item dependencies
    # under the extraction budget, including the final serialization work.
    # No descriptor, SQLite transaction, executable owner, or lazy materializer
    # escapes this call. Sidecar writes begin only after this result exists.
    return {
        "values": values,
        "source_pair_refs": sources,
        "coverage": coverage,
        "envelope": {"dependencies": dependencies, "private_scope": None},
        "extraction_version": EXTRACTION_VERSION,
        "sources_closed": True,
    }
