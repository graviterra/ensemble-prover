"""Exact compatibility fingerprint for a Mini theory Lean environment."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any, Optional

from .model import content_hash
from ..subprocess_environment import sanitized_subprocess_environment


def dependency_environment_fingerprint(lean_project_dir: Path) -> str:
    """Hash the resolved Lake graph and reject incomplete/dirty checkouts.

    A Mathlib HEAD alone is insufficient: transitive package revisions and a
    changed resolved manifest can alter elaboration.  Returning an empty
    fingerprint fails publication/reuse closed when the environment is not a
    clean realization of its committed Lake manifest.
    """

    project = Path(lean_project_dir).expanduser().resolve()
    manifest_path = project / "lake-manifest.json"
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, ValueError, TypeError):
        return ""
    packages = manifest.get("packages")
    packages_dir = str(manifest.get("packagesDir") or ".lake/packages").strip()
    if not isinstance(packages, list) or not packages_dir:
        return ""
    if any(not isinstance(item, dict) for item in packages):
        return ""
    realized: list[dict[str, Any]] = []
    for package in sorted(
        packages,
        key=lambda item: str(item.get("name") or ""),
    ):
        name = str(package.get("name") or "").strip()
        package_type = str(package.get("type") or "").strip()
        expected_revision = str(package.get("rev") or "").strip()
        if not name or package_type != "git" or not expected_revision:
            return ""
        checkout = (project / packages_dir / name).resolve()
        try:
            checkout.relative_to((project / packages_dir).resolve())
        except ValueError:
            return ""
        if not checkout.is_dir():
            return ""
        head = _git_output(checkout, "rev-parse", "HEAD")
        dirty = _git_output(checkout, "status", "--porcelain")
        if head is None or dirty is None or head != expected_revision or dirty:
            return ""
        realized.append(
            {
                "name": name,
                "revision": head,
                "url": str(package.get("url") or ""),
                "scope": str(package.get("scope") or ""),
            }
        )
    # The original persistent-store contract hashed the complete Putnam Lake
    # manifest.  Keep that byte-for-byte bucket identity while normalizing the
    # two root-only fields that legitimately change when Mini is moved into its
    # own repository.  Dependency entries and every other manifest field remain
    # compatibility-significant and therefore fail closed on any change.
    canonical_manifest = dict(manifest)
    canonical_manifest["name"] = "putnam"
    canonical_manifest["lakeDir"] = ".lake"
    payload = json.dumps(
        {
            "manifest": canonical_manifest,
            "realized_packages": realized,
        },
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    )
    return content_hash(payload, length=64)


def _git_output(root: Path, *args: str) -> Optional[str]:
    try:
        run = subprocess.run(
            ["git", *args],
            cwd=root,
            env=sanitized_subprocess_environment(),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
    except OSError:
        return None
    return run.stdout.strip() if run.returncode == 0 else None
