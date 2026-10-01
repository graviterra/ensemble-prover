"""Exact compatibility fingerprint for a Mini theory Lean environment."""

from __future__ import annotations

import json
import os
import signal
import subprocess
import tempfile
import time
from contextlib import contextmanager, nullcontext
from contextvars import ContextVar
from pathlib import Path
from types import SimpleNamespace
from typing import Any, Mapping, Optional

from .model import content_hash
from ..subprocess_environment import sanitized_subprocess_environment


_FINGERPRINT_OWNER: ContextVar[tuple[tuple[Any, ...], float | None]] = ContextVar(
    "theory_fingerprint_owner", default=((), None)
)
_GIT_OUTPUT_LIMIT = 1024 * 1024


@contextmanager
def environment_fingerprint_scope(
    *, cancellation_event: Any, deadline_monotonic: float
):
    """Carry the research worker's owner through synchronous preflight calls."""
    events, inherited = _FINGERPRINT_OWNER.get()
    deadline = (
        min(inherited, deadline_monotonic)
        if inherited is not None
        else deadline_monotonic
    )
    token = _FINGERPRINT_OWNER.set(((*events, cancellation_event), deadline))
    try:
        yield
    finally:
        _FINGERPRINT_OWNER.reset(token)


def _check_fingerprint_owner() -> float | None:
    from ..lean_runner import current_lean_deadline

    events, deadline = _FINGERPRINT_OWNER.get()
    lean_deadline = current_lean_deadline()
    if lean_deadline is not None:
        deadline = (
            min(deadline, lean_deadline) if deadline is not None else lean_deadline
        )
    if any(event.is_set() for event in events) or (
        deadline is not None and time.monotonic() >= deadline
    ):
        raise TimeoutError("theory environment owner allocation exhausted")
    return deadline


def dependency_environment_fingerprint(lean_project_dir: Path) -> str:
    """Hash the resolved Lake graph and reject incomplete/dirty checkouts.

    A Mathlib HEAD alone is insufficient: transitive package revisions and a
    changed resolved manifest can alter elaboration.  Returning an empty
    fingerprint fails publication/reuse closed when the environment is not a
    clean realization of its committed Lake manifest.
    """

    _check_fingerprint_owner()
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
        _check_fingerprint_owner()
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
    deadline = _check_fingerprint_owner()
    if deadline is not None or _FINGERPRINT_OWNER.get()[0]:
        return _owned_git_output(root, args, deadline)
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


def _owned_git_output(
    root: Path,
    args: tuple[str, ...],
    deadline: float | None,
    *,
    environment: Mapping[str, str] | None = None,
    acquire_process_slot: bool = True,
) -> Optional[str]:
    from ..lean_runner import bounded_lean_process_command, lean_process_slot
    from ..local_inference.network_policy import prepare_owned_subprocess

    command = ("git", *args)
    events = _FINGERPRINT_OWNER.get()[0]
    cancellation = SimpleNamespace(
        is_set=lambda: any(event.is_set() for event in events)
    )
    # Spawn preflights run synchronously before the enclosing slot's main
    # process exists; they must not acquire that same finite slot again.
    slot = (
        lean_process_slot(deadline=deadline, cancellation_event=cancellation)
        if acquire_process_slot
        else nullcontext()
    )

    def check_owner() -> None:
        _check_fingerprint_owner()
        if deadline is not None and time.monotonic() >= deadline:
            raise TimeoutError("theory environment owner allocation exhausted")

    try:
        with slot, tempfile.TemporaryFile() as output:
            check_owner()
            process = subprocess.Popen(
                bounded_lean_process_command(command),
                cwd=root,
                env=prepare_owned_subprocess(
                    command, project=root, kind="local_tool", base=environment
                ),
                stdout=output,
                stderr=subprocess.DEVNULL,
                start_new_session=True,
            )
            try:
                while process.poll() is None:
                    check_owner()
                    if os.fstat(output.fileno()).st_size > _GIT_OUTPUT_LIMIT:
                        raise TimeoutError("theory environment output limit exhausted")
                    time.sleep(0.005)
                check_owner()
                output.seek(0)
                raw = output.read(_GIT_OUTPUT_LIMIT + 1)
                if len(raw) > _GIT_OUTPUT_LIMIT or process.returncode != 0:
                    return None
                return raw.decode("utf-8", errors="replace").strip()
            finally:
                # A successful Git parent may leave hooks or helpers behind.
                # The process group remains owned until every terminal path
                # requests its termination and reaps the direct child.
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
    except TimeoutError:
        raise
    except OSError:
        return None
