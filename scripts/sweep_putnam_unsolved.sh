#!/usr/bin/env bash
set -euo pipefail
sweep_repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$sweep_repo_root"
exec "$sweep_repo_root/.venv/bin/python" -m ensemble_prover.putnam_sweep "$@"
