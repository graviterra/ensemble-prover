"""Separate research context from an explicit candidate for paid proof work."""

from typing import Any


def is_proof_candidate(action: Any) -> bool:
    """Recognize candidate intent, without judging mathematical correctness.

    Reports, gaps, and reviews remain useful context. Only an explicit plan
    or submitted argument requests another proof attempt under existing limits.
    """
    if not isinstance(action, dict):
        return False
    if action.get("action") == "formalize":
        content = action.get("proof_plan")
    elif (action.get("action") == "submit"
          and action.get("kind") in ("written_proof", "counterexample")):
        content = action.get("content")
    else:
        return False
    return isinstance(content, str) and bool(content.strip())
