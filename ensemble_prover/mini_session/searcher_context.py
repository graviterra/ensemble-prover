"""In-process retrieval visibility isolation for child Mini sessions."""

from __future__ import annotations

from typing import Any


def fork_searcher_context(searcher: Any, *, theory_enabled: bool) -> Any:
    """Return a child-local retrieval view when the backend supports one."""

    if searcher is None:
        return None
    fork = getattr(searcher, "fork_session_context", None)
    if callable(fork):
        child_searcher = fork()
        if child_searcher is None:
            raise RuntimeError("recursive child searcher fork returned None")
        if (
            child_searcher is searcher
            and theory_enabled
            and callable(getattr(searcher, "set_active_bundle_ids", None))
        ):
            raise RuntimeError(
                "recursive child searcher fork did not isolate theory visibility"
            )
        return child_searcher
    if theory_enabled and callable(
        getattr(searcher, "set_active_bundle_ids", None)
    ):
        raise RuntimeError(
            "theory-enabled recursive child requires an isolated searcher context"
        )
    return searcher
