"""Count budgets with an explicit unlimited sentinel.

Negative one means no cumulative count limit. Zero retains its ordinary meaning
of no allocated work. Scheduling batches remain finite independently of these
run and conversation budgets.
"""


def add_count_limits(*limits: int) -> int:
    """Combine allocations without turning an unlimited allocation into zero."""
    if any(limit < 0 for limit in limits):
        return -1
    return sum(limits)

