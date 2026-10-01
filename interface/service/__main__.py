"""Serve the product interface on loopback.

``python -m interface.service`` binds to ``127.0.0.1`` only. Attempt launch
and cooperative stop stay disabled unless ``--control`` is passed.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

import uvicorn

from .app import create_app
from .catalog import default_run_root
from .security import browser_boundary
from .memory import DEFAULT_MEMORY_ROOT

DEFAULT_PORT = 8765
LOOPBACK_HOST = "127.0.0.1"
_UI_DIST = Path(__file__).resolve().parent.parent / "web" / "dist"


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="python -m interface.service",
        description=(
            "Serve the Ensemble Prover library and attempt view on 127.0.0.1. "
            "Launch and stop stay off unless --control is set."
        ),
    )
    parser.add_argument(
        "--run-root",
        type=Path,
        default=None,
        help="trusted directory of prover run folders (default: repository runs/mini_prover, including linked worktrees)",
    )
    parser.add_argument(
        "--state-root",
        type=Path,
        default=Path.home() / ".ensemble_prover_interface",
        help="launch registry and service logs, outside run directories",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path("."),
        help="repository containing the prover package and .venv (default: cwd)",
    )
    parser.add_argument(
        "--port",
        type=int,
        default=DEFAULT_PORT,
        help=f"loopback TCP port (default: {DEFAULT_PORT})",
    )
    parser.add_argument("--memory-root", type=Path, default=DEFAULT_MEMORY_ROOT,
                        help="trusted mathematical-memory catalog; must match the run's recorded configuration")
    parser.add_argument(
        "--control",
        action="store_true",
        help="enable attempt launch and one confirmed cooperative stop",
    )
    parser.add_argument(
        "--api-only", action="store_true",
        help="serve only the API, for use with the local development server",
    )
    parser.add_argument(
        "--web-origin",
        help="explicit local development origin, for example http://127.0.0.1:5173",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.port < 1 or args.port > 65535:
        print("port must be between 1 and 65535", file=sys.stderr)
        return 2
    try:
        browser_boundary(args.port, args.web_origin)
    except ValueError as exc:
        print(str(exc), file=sys.stderr)
        return 2
    if not args.api_only and not (_UI_DIST / "index.html").is_file():
        print(
            "The browser page has not been built. From the repository root run:\n"
            "  cd interface/web\n  npm ci\n  npm run build\n"
            "Then start this service again from the repository root. "
            "See interface/README.md for setup, or use --api-only with the development server.",
            file=sys.stderr,
        )
        return 2
    app = create_app(
        run_root=args.run_root if args.run_root is not None else default_run_root(args.repo_root),
        state_root=args.state_root,
        repo_root=args.repo_root,
        control=bool(args.control),
        port=args.port,
        web_origin=args.web_origin,
        serve_ui=not args.api_only,
        memory_root=args.memory_root,
    )
    uvicorn.run(app, host=LOOPBACK_HOST, port=args.port)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
