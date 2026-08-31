#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VENV_DIR="${ROOT_DIR}/.venv"

inspect_runtime() {
  local candidate="$1"
  PYTHON_IMPLEMENTATION="$("${candidate}" -c 'import sys; print(sys.implementation.name)' 2>/dev/null)" || return 1
  PYTHON_VERSION="$("${candidate}" -c 'import sys; print(f"{sys.version_info.major}.{sys.version_info.minor}")' 2>/dev/null)" || return 1
  PYTHON_TRACE_REFS="$("${candidate}" -c 'import sys; print(str(hasattr(sys, "getobjects")).lower())' 2>/dev/null)" || return 1
}

runtime_is_supported() {
  local candidate="$1"
  inspect_runtime "${candidate}" || return 1
  [ "${PYTHON_IMPLEMENTATION}" = "cpython" ] || return 1
  case "${PYTHON_VERSION}" in
    3.11|3.12) ;;
    *) return 1 ;;
  esac
  [ "${PYTHON_TRACE_REFS}" = "false" ]
}

PYTHON_BIN="${PYTHON_BIN:-}"
if [ -z "${PYTHON_BIN}" ]; then
  for candidate in python3.12 python3.11 python3; do
    if command -v "${candidate}" >/dev/null 2>&1 && runtime_is_supported "${candidate}"; then
      PYTHON_BIN="${candidate}"
      break
    fi
  done
  if [ -z "${PYTHON_BIN}" ]; then
    echo "A standard CPython 3.11 or 3.12 runtime is required for exact rollback support." >&2
    exit 1
  fi
elif ! inspect_runtime "${PYTHON_BIN}"; then
  echo "Unable to inspect the requested Python runtime: ${PYTHON_BIN}." >&2
  exit 1
fi

if [ "${PYTHON_IMPLEMENTATION}" != "cpython" ]; then
  echo "CPython 3.11 or 3.12 is required for exact rollback support; got ${PYTHON_IMPLEMENTATION}." >&2
  exit 1
fi
case "${PYTHON_VERSION}" in
  3.11|3.12) ;;
  *)
    echo "CPython 3.11 or 3.12 is required for exact rollback support; got ${PYTHON_VERSION}." >&2
    exit 1
    ;;
esac
if [ "${PYTHON_TRACE_REFS}" = "true" ]; then
  echo "A standard CPython object layout is required; trace-reference builds are unsupported." >&2
  exit 1
fi

"${PYTHON_BIN}" -m venv "${VENV_DIR}"
source "${VENV_DIR}/bin/activate"
pip install --upgrade pip
pip install -r "${ROOT_DIR}/requirements.txt"

echo "Venv ready at ${VENV_DIR} (python: ${PYTHON_BIN})"
