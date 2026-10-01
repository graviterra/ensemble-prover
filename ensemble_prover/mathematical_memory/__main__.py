"""Explicit local catalog maintenance: python -m ensemble_prover.mathematical_memory."""

from __future__ import annotations
import argparse
import json
from .catalog import MemoryCatalog, MemoryUnavailable


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Inspect or maintain an explicit local mathematical memory catalog"
    )
    parser.add_argument("--root", required=True)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("inspect")
    backup = commands.add_parser("backup")
    backup.add_argument("destination")
    restore = commands.add_parser("restore")
    restore.add_argument("backup")
    rebuild = commands.add_parser("rebuild")
    rebuild.add_argument("--destination")
    drain = commands.add_parser("drain")
    drain.add_argument("--limit", type=int, default=64)
    args = parser.parse_args(argv)
    try:
        if args.command == "restore":
            catalog = MemoryCatalog.restore(args.backup, args.root)
            result = catalog.inspect()
        else:
            catalog = MemoryCatalog(args.root, read_only=args.command == "inspect")
            if args.command == "inspect":
                result = catalog.inspect()
            elif args.command == "backup":
                result = {"backup": str(catalog.backup(args.destination))}
            elif args.command == "rebuild":
                result = catalog.rebuild(args.destination).inspect()
            else:
                result = {
                    "deliveries": [
                        entry.__dict__
                        for entry in catalog.drain_outbox(limit=args.limit)
                    ]
                }
        print(json.dumps(result, ensure_ascii=False, sort_keys=True))
        return 0
    except (MemoryUnavailable, OSError, ValueError) as exc:
        print(json.dumps({"status": "unavailable", "diagnostic": str(exc)}))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
