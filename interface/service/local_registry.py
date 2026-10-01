"""Operator-owned local deployment registry for the browser service.

Load one strict profile at startup. Later catalog and launch reads use that
object. They do not probe endpoints, open sockets, or publish URLs, credential
names, configuration paths, or private snapshots.
"""

from __future__ import annotations

from pathlib import Path
import os
import stat
import re
from typing import Any

from ensemble_prover.local_inference.config import ProfileDocument, load_profile_path
from ensemble_prover.local_inference.strictload import atomic_write_json, content_hash, read_json_object

ENV_CONFIG = "ENSEMBLE_LOCAL_INFERENCE_CONFIG"
CURSOR_BIN = "agent"
CURSOR_UNAVAILABLE = (
    "The installed Cursor CLI is unqualified for prover generation. "
    "Startup hooks outside CURSOR_CONFIG_DIR are not suppressed, and context preservation is not established. "
    "An exact model name is required. Auto and the CLI default are not used. "
    "This check does not start the agent."
)
_DEPLOYMENT_ID = re.compile(r"[A-Za-z_][A-Za-z0-9_-]{0,63}\Z")
_CURSOR_MODEL = re.compile(r"[A-Za-z0-9][A-Za-z0-9._:/-]{0,255}\Z")
_FLAGS = {
    "prover": ("--prover", "--prover-deployment", "--prover-model"),
    "refiner": ("--refiner", "--refiner-deployment", "--refiner-model"),
    "formalizer": ("--formalizer", "--formalizer-deployment", "--formalizer-model"),
}
_PUBLIC = {
    "profile_unconfigured": "No operator local profile is configured.",
    "unknown_deployment": "Choose a registered local deployment.",
    "model_conflict": "A local deployment supplies its model. Remove the conflicting model override.",
    "local_only_formalizer": "English with local-only inference requires a local formalizer deployment.",
    "hosted_upstream_forbidden": "Local-only inference requires an operator-asserted local deployment.",
    "cursor_model": "Cursor requires an exact model name. Auto and the CLI default are not accepted.",
    "snapshot_unavailable": "The saved operator profile is unavailable or has changed. Restart the service to reload its configuration.",
    "local_only_provider": "Local-only inference requires local deployments for every enabled role.",
    "deployment_forbidden": "A deployment id is only accepted for the local provider.",
}


class LocalRegistryError(ValueError):
    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(_PUBLIC.get(code, "The local deployment selection was rejected."))

    @property
    def public_message(self) -> str:
        return str(self)


class OperatorLocalRegistry:
    def __init__(self, path: Path | None, document: ProfileDocument | None, snapshot_directory: Path | None = None) -> None:
        self._path = path
        self._document = document
        self._snapshot_directory = snapshot_directory

    @property
    def loaded(self) -> bool:
        return self._document is not None and self._path is not None

    @classmethod
    def load(cls, source: str | Path | None, *, snapshot_directory: Path | None = None) -> "OperatorLocalRegistry":
        if isinstance(source, Path):
            text = str(source).strip()
        elif isinstance(source, str):
            text = source.strip()
        elif source is None:
            text = ""
        else:
            raise LocalRegistryError("profile_unconfigured")
        if not text:
            return cls(None, None)
        path = Path(text).expanduser()
        document = load_profile_path(path)
        return cls(path.resolve(), document, snapshot_directory)

    def public_deployments(self) -> list[dict[str, Any]]:
        if self._document is None:
            return []
        private = [endpoint.base_url for endpoint in self._document.endpoints.values()]
        private.extend(
            endpoint.auth.name for endpoint in self._document.endpoints.values() if endpoint.auth.name
        )
        if self._path is not None:
            private.append(str(self._path))
        rows: list[dict[str, Any]] = []
        for deployment in self._document.deployments.values():
            endpoint = self._document.endpoints[deployment.endpoint]
            row = {
                "id": deployment.name,
                "model": deployment.model,
                "contextTokens": deployment.context_tokens,
                "maxOutputTokens": deployment.max_output_tokens,
                "tools": deployment.tools,
                "reasoningMode": deployment.reasoning.mode,
                "reasoningEffort": deployment.reasoning.effort or "",
                "outputLimitIncludesReasoning": deployment.reasoning.output_limit_includes_reasoning,
                "execution": deployment.execution,
                "dialect": endpoint.dialect,
                "capability": "declared",
                "probed": False,
                "availability": "Declared in the operator profile and not probed.",
            }
            encoded = repr(row)
            if any(item and item in encoded for item in private):
                continue
            rows.append(row)
        return rows

    def config_flags(self) -> list[str]:
        if self._document is None or self._snapshot_directory is None:
            raise LocalRegistryError("profile_unconfigured")
        body = self._document.canonical_body()
        target = self._snapshot_directory / (content_hash(body) + ".json")
        try:
            self._snapshot_directory.mkdir(parents=True, exist_ok=True, mode=0o700)
            if target.exists() or target.is_symlink():
                mode = target.lstat().st_mode
                if not stat.S_ISREG(mode) or stat.S_IMODE(mode) & 0o077:
                    raise ValueError("snapshot")
                saved = read_json_object(target, max_bytes=1024 * 1024, corrupt_code="invalid_profile")
                if content_hash(saved) != content_hash(body):
                    raise ValueError("snapshot")
            else:
                atomic_write_json(target, body, max_bytes=1024 * 1024)
                os.chmod(target, 0o600)
        except Exception:
            raise LocalRegistryError("snapshot_unavailable") from None
        return ["--local-inference-config", str(target)]

    def local_flags(self, role: str, deployment_id: str, model: str) -> list[str]:
        provider_flag, deployment_flag, _model_flag = _FLAGS[role]
        if not self.loaded or self._document is None:
            raise LocalRegistryError("profile_unconfigured")
        if not isinstance(deployment_id, str) or _DEPLOYMENT_ID.fullmatch(deployment_id) is None:
            raise LocalRegistryError("unknown_deployment")
        deployment = self._document.deployments.get(deployment_id)
        if deployment is None:
            raise LocalRegistryError("unknown_deployment")
        if model and model != deployment.model:
            raise LocalRegistryError("model_conflict")
        return [provider_flag, "local", deployment_flag, deployment.name]

    def assert_local_execution(self, deployment_id: str) -> None:
        if self._document is None:
            raise LocalRegistryError("profile_unconfigured")
        deployment = self._document.deployments.get(deployment_id)
        if deployment is None:
            raise LocalRegistryError("unknown_deployment")
        if deployment.execution != "operator_asserted_local":
            raise LocalRegistryError("hosted_upstream_forbidden")


def cursor_flags(role: str, model: str) -> list[str]:
    provider_flag, _deployment_flag, model_flag = _FLAGS[role]
    if (
        not isinstance(model, str)
        or not model.strip()
        or model.lower() == "auto"
        or _CURSOR_MODEL.fullmatch(model) is None
    ):
        raise LocalRegistryError("cursor_model")
    return [provider_flag, "cursor", model_flag, model]
