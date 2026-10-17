"""Explicit local commands for authorized offline research views.

The policy file is host configuration. Command input cannot supply a visibility
envelope, a principal, or a claim that its authoring provenance is complete.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import stat
import sqlite3
from typing import Any, Sequence

from .policy import AccessContext, HostPolicy
from .references import ProjectionError
from .source_reader import read_owner_inputs
from .view_store import ViewStore


def _json_file(path: str, *, trusted: bool = False) -> Any:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | os.O_NONBLOCK
    fd = os.open(path, flags)
    with os.fdopen(fd, "rb") as stream:
        info = os.fstat(stream.fileno())
        if not stat.S_ISREG(info.st_mode):
            raise ValueError("regular JSON file required")
        if trusted and (info.st_uid != os.getuid() or info.st_mode & 0o077):
            raise ValueError("policy must be owned by this user with mode 0600")
        limit = 64 * 1024 if trusted else 4 * 1024 * 1024
        payload = stream.read(limit + 1)
        if len(payload) > limit:
            raise ValueError("JSON file exceeds input limit")
        return json.loads(payload)


def _configuration(path: str) -> tuple[dict[str, Any], HostPolicy, AccessContext]:
    config = _json_file(path, trusted=True)
    if not isinstance(config, dict) or config.get("format_version") != 1:
        raise ValueError("unsupported policy format")
    allowed = {"format_version", "sidecar", "sources", "source_roots", "scanner_roots",
               "scope", "redactions", "max_storage_bytes", "max_source_bytes", "timeout_seconds"}
    if set(config) - allowed:
        raise ValueError("unknown policy setting")
    if not isinstance(config.get("scope"), str) or not config["scope"]:
        raise ValueError("private authoring scope required")
    sources = config.get("sources")
    if not isinstance(sources, dict) or set(sources) - {"proof", "research"} or not sources:
        raise ValueError("configure proof and/or research sources")
    namespaces = set()
    for source in sources.values():
        if (not isinstance(source, dict) or set(source) != {"path", "namespace"}
                or not all(isinstance(source[key], str) and source[key] for key in source)):
            raise ValueError("source needs a path and namespace")
        if not Path(source["path"]).is_absolute():
            raise ValueError("source paths must be absolute")
        if source["namespace"] in namespaces:
            raise ValueError("source namespaces must be distinct")
        namespaces.add(source["namespace"])
    for key in ("source_roots", "scanner_roots"):
        roots = config.get(key)
        if not isinstance(roots, list) or (key == "source_roots" and not roots):
            raise ValueError("explicit source and scanner roots required")
        if any(not isinstance(root, str) or not Path(root).is_absolute() for root in roots):
            raise ValueError("roots must be absolute paths")
    if not isinstance(config.get("sidecar"), str) or not Path(config["sidecar"]).is_absolute():
        raise ValueError("explicit absolute sidecar path required")
    redactions = config.get("redactions", [])
    if not isinstance(redactions, list) or any(not isinstance(item, str) or not item for item in redactions):
        raise ValueError("redactions must be nonempty literal strings")
    principal = f"uid:{os.getuid()}"
    context = AccessContext(
        principal=principal, role="operator", audience="operator", scope=config["scope"],
    )

    def authorize(dependency: dict[str, Any], caller: AccessContext) -> bool:
        return (caller == context and dependency.get("namespace") in namespaces)

    def redact(text: str, caller: AccessContext) -> str:
        for secret in sorted(redactions, key=len, reverse=True):
            text = text.replace(secret, "[redacted]")
        return text

    return config, HostPolicy(authorize=authorize, redact=redact), context


def _store(config: dict[str, Any], *, create: bool) -> ViewStore:
    roots = list(config["source_roots"])
    # Source files are protected even if the operator omitted their parent from
    # the broader run, artifact, and mathematical-memory scan roots.
    for source in config["sources"].values():
        path = Path(source["path"])
        roots.append(str(path if path.is_dir() else path.parent))
    return ViewStore(config["sidecar"], source_roots=roots,
                     scanner_roots=config["scanner_roots"], create=create,
                     max_storage_bytes=config.get("max_storage_bytes", 512 * 1024 * 1024))


def _handle(path: str, key: str) -> dict[str, Any]:
    value = _json_file(path)
    if not isinstance(value, dict):
        raise ValueError("reference must be an object")
    ref = value.get(key, value)
    if not isinstance(ref, dict):
        raise ValueError("reference must be an object")
    return ref


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", required=True, help="Private host policy JSON (mode 0600)")
    sub = parser.add_subparsers(dest="command", required=True)
    create = sub.add_parser("create", help="Install a view of configured committed source copies")
    create.add_argument("--offline", action="store_true", required=True,
                        help="Attest sources are independent quiescent copies or consistent exports")
    for command in ("read", "delete"):
        item = sub.add_parser(command, help=f"{command.capitalize()} an installed view")
        item.add_argument("reference", help="View reference JSON file")
    page = sub.add_parser("page", help="Select a value and issue an exact page reference")
    page.add_argument("reference")
    page.add_argument("--path", default="[]", help="JSON list of object keys and list indexes")
    page.add_argument("--offset", type=int, default=0)
    page.add_argument("--length", type=int, default=6000)
    page.add_argument("--transform", default="json-v1", choices=("text-v1", "json-v1"))
    resolve = sub.add_parser("resolve", help="Resolve an issued page without consulting current source rows")
    resolve.add_argument("reference")
    search = sub.add_parser("search", help="Find retained records and their exact expansion paths")
    search.add_argument("reference")
    search.add_argument("query")
    search.add_argument("--limit", type=int, default=50)
    propose = sub.add_parser("propose", help="Save explicit advisory associations")
    propose.add_argument("input", help="JSON command with command_id, proposals and authoring_refs")
    relations = sub.add_parser("relations", help="List authorized advisory associations")
    relations.add_argument("--query", default="")
    relation = sub.add_parser("relation", help="Read an exact advisory revision")
    relation.add_argument("reference")
    argument = sub.add_parser("argument", help="Read an exact complete association argument")
    argument.add_argument("reference")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        config, policy, context = _configuration(args.config)
        store = _store(config, create=args.command in {"create", "propose"})
        result = _execute(args, config, store, policy, context)
    except ProjectionError as exc:
        result = {"status": exc.code}
    except sqlite3.Error:
        result = {"status": "observation_unavailable"}
    except (OSError, ValueError, TypeError, KeyError, OverflowError, RecursionError):
        result = {"status": "invalid_request"}
    print(json.dumps(result, ensure_ascii=False, sort_keys=True, allow_nan=False))
    return 0 if result.get("status") in {"ok", "saved", "already_saved", "deleted"} else 1


def _execute(args: argparse.Namespace, config: dict[str, Any], store: ViewStore,
             policy: HostPolicy, context: AccessContext) -> dict[str, Any]:
    if args.command == "create":
        sources = config["sources"]
        proof = sources.get("proof", {})
        research = sources.get("research", {})
        snapshot = read_owner_inputs(
            proof_path=proof.get("path"), research_path=research.get("path"),
            proof_source_id=proof.get("namespace", "proof"),
            research_source_id=research.get("namespace", "research"),
            policy=policy, context=context, offline=args.offline,
            max_bytes=config.get("max_source_bytes", 64 * 1024 * 1024),
            timeout_seconds=config.get("timeout_seconds", 10.0),
        )
        from .associations import AssociationStore
        snapshot = AssociationStore(store).project_into(snapshot, policy=policy, context=context)
        return store.materialize_view(snapshot, policy=policy, context=context)
    if args.command == "read":
        return store.read_view(_handle(args.reference, "view_ref"), policy=policy, context=context)
    if args.command == "delete":
        return store.delete_view(_handle(args.reference, "view_ref"), policy=policy, context=context)
    if args.command == "search":
        from .inspection import search_view
        return search_view(store, _handle(args.reference, "view_ref"), args.query,
                           limit=args.limit, policy=policy, context=context)
    if args.command in {"page", "resolve"}:
        from .render import issue_page, read_view_page
        if args.command == "resolve":
            return read_view_page(store, _handle(args.reference, "page_ref"), policy=policy, context=context)
        return issue_page(store, _handle(args.reference, "view_ref"), path=json.loads(args.path),
                          start=args.offset, limit=args.length, transform=args.transform,
                          policy=policy, context=context)
    from .associations import AssociationStore
    associations = AssociationStore(store)
    if args.command == "propose":
        command = _json_file(args.input)
        if not isinstance(command, dict) or set(command) - {"command_id", "proposals", "authoring_refs"}:
            raise ValueError("invalid association command")
        return associations.write_command(command["command_id"], command["proposals"],
                                          authoring_refs=command.get("authoring_refs", []),
                                          provenance_complete=False, policy=policy, context=context)
    if args.command == "relations":
        return associations.search(args.query, policy=policy, context=context)
    if args.command == "relation":
        return associations.read(_handle(args.reference, "association_ref"), policy=policy, context=context)
    return associations.read_argument(_handle(args.reference, "argument_ref"), policy=policy, context=context)
