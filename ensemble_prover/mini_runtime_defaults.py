"""Shared runtime defaults for Mini's formal proof operations."""

from __future__ import annotations


# Twelve seconds was shorter than a normal 36-candidate Lean tactic portfolio
# on nontrivial goals and caused cancellation/retry loops.  Keep an operation
# watchdog, but give a frontier proof probe enough time to finish useful work.
DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S = 120.0

# This quantum is also the aggregate child-closure deadline when formal search
# is enabled, so keep it aligned with the proof-state probe watchdog.
DEFAULT_FORMAL_STATE_SEARCH_TOTAL_TIMEOUT_S = 120.0

# Zero means: do not asyncio-cancel an in-flight Lean check. A 15s knife
# detached the wrapper, discarded a late result, and left the shared lock
# held with no Lean child — then verify_with_lean waited forever.
# The search quantum still yields between steps via total_timeout_s.
DEFAULT_FORMAL_STATE_SEARCH_OPERATION_TIMEOUT_S = 0.0

# Goal-conditioned policy calls emit a short tactic list.  Keep their model
# capability independent from full proof-authoring capacity so a single search
# step cannot consume a multi-minute hidden-reasoning completion.
DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_TIMEOUT_S = 45.0
DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_MAX_TOKENS = 768
DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT = "none"
