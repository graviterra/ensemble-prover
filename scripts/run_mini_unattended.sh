#!/usr/bin/env bash
# Bound unattended single-problem runs; explicit CLI arguments below win.
set -euo pipefail

MINI_REPO_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "${MINI_REPO_ROOT}"
exec "${MINI_REPO_ROOT}/.venv/bin/python" -m ensemble_prover.mini_prover \
  --mini-worker-timeout-s 7200 \
  --mini-run-wall-clock-budget-s 6900 \
  --mini-no-strong-progress-budget-s 1800 \
  "$@"
