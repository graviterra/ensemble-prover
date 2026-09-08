"""Validate the exact advisory artifact prepared for a native worker launch."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
from typing import Any

_STARTUP_SIDECAR = "theory_promotion_maintenance.json"


def startup_artifact_receipts(directory: Path, *, nonce: str) -> dict[str, str]:
    path = Path(directory) / _STARTUP_SIDECAR
    if not path.exists():
        return {}
    if path.is_symlink() or not path.is_file():
        raise ValueError("Startup artifact must be a regular file")
    content = path.read_bytes()
    try:
        record = json.loads(content)
    except (ValueError, UnicodeError) as error:
        raise ValueError("Invalid native startup artifact") from error
    promotion = record.get("mini_theory_promotion") if type(record) is dict else None
    if (re.fullmatch(r"[0-9a-f]{32}", str(nonce or "")) is None
            or type(record) is not dict or record.get("schema_version") != 1
            or record.get("summary_sha256") != ""
            or type(promotion) is not dict
            or promotion.get("maintenance_owner") != "pre_worker_supervisor"
            or promotion.get("startup_overlay_nonce") != nonce):
        raise ValueError("Startup artifact does not belong to this fresh native launch")
    return {_STARTUP_SIDECAR: hashlib.sha256(content).hexdigest()}


def validate_startup_artifact_receipts(directory: Path, receipts: Any) -> set[str]:
    """Keep directory exceptions restricted to unchanged, attested sidecars."""
    if receipts is None:
        return set()
    if type(receipts) is not dict or not set(receipts) <= {_STARTUP_SIDECAR}:
        raise ValueError("Invalid startup artifact receipt set")
    for name, digest in receipts.items():
        path = Path(directory) / name
        if (type(digest) is not str or re.fullmatch(r"[0-9a-f]{64}", digest) is None
                or path.is_symlink() or not path.is_file()
                or hashlib.sha256(path.read_bytes()).hexdigest() != digest):
            raise ValueError("Startup artifact changed after launch validation")
    return set(receipts)
