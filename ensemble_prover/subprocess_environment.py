"""Environment policy for child processes started by Ensemble Prover.

Lean elaboration can execute user-supplied code.  Child processes therefore
receive a copy of the current environment with credential-like variables
removed unless they are an explicitly trusted internal provider worker.
"""

from __future__ import annotations

import ctypes
import os
import sys
from collections.abc import Mapping
from typing import Optional
from urllib.parse import parse_qsl, urlsplit


_SENSITIVE_EXACT_NAMES = frozenset(
    {
        "AWS_ACCESS_KEY_ID",
        "AWS_SECRET_ACCESS_KEY",
        "AWS_SESSION_TOKEN",
        "AWS_WEB_IDENTITY_TOKEN_FILE",
        "ACCESS_KEY",
        "API_KEY",
        "AZURE_CLIENT_CERTIFICATE_PATH",
        "AZURE_FEDERATED_TOKEN_FILE",
        "CONNECTION_STRING",
        "CREDENTIAL",
        "CREDENTIALS",
        "DOCKER_AUTH_CONFIG",
        "DOCKER_CONFIG",
        "GIT_ASKPASS",
        "GITHUB_TOKEN",
        "GH_TOKEN",
        "GITLAB_TOKEN",
        "GOOGLE_APPLICATION_CREDENTIALS",
        "HF_TOKEN",
        "HUGGING_FACE_HUB_TOKEN",
        "KUBECONFIG",
        "MYSQL_PWD",
        "NETRC",
        "NPM_CONFIG__AUTH",
        "NPM_CONFIG_USERCONFIG",
        "PASSWORD",
        "PASSWD",
        "PGPASSWORD",
        "PRIVATE_KEY",
        "REDISCLI_AUTH",
        "SECRET",
        "SSH_ASKPASS",
        "SSH_AGENT_PID",
        "SSH_AUTH_SOCK",
        "TOKEN",
    }
)
_SENSITIVE_NAME_SUFFIXES = (
    "_ACCESS_KEY",
    "_API_KEY",
    "_CREDENTIAL",
    "_CREDENTIALS",
    "_CONNECTION_STRING",
    "_DSN",
    "_PASSWORD",
    "_PRIVATE_KEY",
    "_SECRET",
    "_TOKEN",
)
_SENSITIVE_URL_QUERY_NAMES = frozenset(
    {
        "access_key",
        "access_token",
        "api_key",
        "apikey",
        "auth",
        "authorization",
        "credential",
        "password",
        "passwd",
        "private_key",
        "secret",
        "signature",
        "token",
    }
)
_SENSITIVE_URL_QUERY_SUFFIXES = (
    "_access_key",
    "_api_key",
    "_credential",
    "_password",
    "_private_key",
    "_secret",
    "_signature",
    "_token",
)
_PR_SET_DUMPABLE = 4


def _protect_linux_parent_environment() -> None:
    """Deny same-UID descendants access to this process via Linux ``/proc``."""

    if sys.platform != "linux":
        return
    try:
        libc = ctypes.CDLL(None, use_errno=True)
        prctl = libc.prctl
        prctl.argtypes = [
            ctypes.c_int,
            ctypes.c_ulong,
            ctypes.c_ulong,
            ctypes.c_ulong,
            ctypes.c_ulong,
        ]
        prctl.restype = ctypes.c_int
        result = prctl(_PR_SET_DUMPABLE, 0, 0, 0, 0)
    except (AttributeError, OSError) as exc:
        raise RuntimeError(
            "unable to protect credential-bearing parent process"
        ) from exc
    if result != 0:
        error_number = ctypes.get_errno()
        raise OSError(
            error_number,
            "unable to protect credential-bearing parent process",
        )


def _value_contains_url_credentials(value: str) -> bool:
    text = str(value or "").strip()
    if "://" not in text:
        return False
    try:
        parsed = urlsplit(text)
        query_names = {
            str(name).strip().lower().replace("-", "_")
            for name, _ in parse_qsl(parsed.query, keep_blank_values=True)
        }
    except ValueError:
        return False
    return (
        parsed.username is not None
        or parsed.password is not None
        or any(
            name in _SENSITIVE_URL_QUERY_NAMES
            or name.endswith(_SENSITIVE_URL_QUERY_SUFFIXES)
            for name in query_names
        )
    )


def _is_sensitive_environment_variable(name: str, value: str) -> bool:
    normalized = str(name).upper()
    return normalized in _SENSITIVE_EXACT_NAMES or normalized.endswith(
        _SENSITIVE_NAME_SUFFIXES
    ) or _value_contains_url_credentials(value)


def _copied_environment(
    base: Optional[Mapping[str, str]],
    *,
    overrides: Optional[Mapping[str, str]],
) -> dict[str, str]:
    child = dict(os.environ if base is None else base)
    if overrides:
        child.update(overrides)
    return child


def sanitized_subprocess_environment(
    base: Optional[Mapping[str, str]] = None,
    *,
    overrides: Optional[Mapping[str, str]] = None,
) -> dict[str, str]:
    """Return a copied child environment with credential variables removed."""

    source = _copied_environment(base, overrides=overrides)
    child = {
        name: value
        for name, value in source.items()
        if not _is_sensitive_environment_variable(name, value)
    }
    if child.keys() != source.keys():
        _protect_linux_parent_environment()
    return child


def trusted_provider_worker_environment(
    base: Optional[Mapping[str, str]] = None,
    *,
    overrides: Optional[Mapping[str, str]] = None,
) -> dict[str, str]:
    """Copy the environment for the trusted internal provider-capable worker.

    This exemption is deliberately narrow: only the watchdog's internal Python
    worker and its supervisor may retain provider credentials.  Lean, Lake,
    solvers, Git, and other child tools must use the sanitized policy instead.
    """

    child = _copied_environment(base, overrides=overrides)
    if any(
        _is_sensitive_environment_variable(name, value)
        for name, value in child.items()
    ):
        _protect_linux_parent_environment()
    return child


__all__ = [
    "sanitized_subprocess_environment",
    "trusted_provider_worker_environment",
]
