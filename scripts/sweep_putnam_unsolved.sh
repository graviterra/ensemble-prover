#!/usr/bin/env bash
# Usage: scripts/sweep_putnam_unsolved.sh [sweep options] -- [MiniProver options]
# Resume with --resume SWEEP_DIR; saved provider arguments and deadlines apply.
# Uses sweep acceptance deadlines; single-run unattended limits are not added.
# Skips all existing exported problems by default; --solved-policy verified opts in
# to the manifest-based filter. Selection does not change proof audit status.
set -euo pipefail
sweep_repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$sweep_repo_root"
# Stream progress to the terminal and the sibling attempt_NNN.sweep_console.log.
export PYTHONUNBUFFERED=1
exec "$sweep_repo_root/.venv/bin/python" -m ensemble_prover.putnam_sweep "$@"
