"""Runtime-only authority for an exact-context Lean proposition check.

These capabilities permit scheduling an unproved proposition. They are never
proof certificates and are intentionally absent from graph records.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Callable


class StatementAdmission(Enum):
    HARD_REJECT = "hard_reject"
    NEEDS_PROP_CHECK = "needs_prop_check"
    PLAUSIBLE = "plausible"
    CHECKED_PROP = "checked_prop"

    @property
    def executable(self) -> bool:
        return self in {self.PLAUSIBLE, self.CHECKED_PROP}


@dataclass(frozen=True, eq=False)
class PropAdmissionContext:
    preamble: str
    helper_blocks: tuple[str, ...]
    environment_stamp: str
    checker_identity: object
    project_identity: str
    toolchain_identity: str
    target_context: str = ""

    def __post_init__(self) -> None:
        if self.checker_identity is None:
            raise ValueError("a proposition admission context requires a live checker")
        if not isinstance(self.helper_blocks, tuple) or any(
            not isinstance(block, str) for block in self.helper_blocks
        ):
            raise TypeError("helper blocks must be an ordered tuple of exact source strings")
        if any(not isinstance(value, str) for value in (
            self.preamble, self.environment_stamp, self.project_identity,
            self.toolchain_identity, self.target_context,
        )):
            raise TypeError("proposition admission context fields must be exact strings")

    def matches(self, other: object) -> bool:
        return bool(
            type(other) is PropAdmissionContext
            and self.checker_identity is other.checker_identity
            and self.preamble == other.preamble
            and self.helper_blocks == other.helper_blocks
            and self.environment_stamp == other.environment_stamp
            and self.project_identity == other.project_identity
            and self.toolchain_identity == other.toolchain_identity
            and self.target_context == other.target_context
        )


@dataclass(frozen=True, eq=False)
class PropAdmissionBinding:
    node: object
    node_id: str
    revision: int
    node_statement: str
    statement: str
    kind: str
    name: str
    source_hash: str

    def matches(self, other: PropAdmissionBinding) -> bool:
        return bool(
            self.node is other.node and self.node_id == other.node_id
            and self.revision == other.revision
            and self.node_statement == other.node_statement
            and self.statement == other.statement and self.kind == other.kind
            and self.name == other.name and self.source_hash == other.source_hash
        )


@dataclass(frozen=True, eq=False)
class PropCheckTicket:
    binding: PropAdmissionBinding
    context: PropAdmissionContext

    @property
    def statement(self) -> str:
        return self.binding.statement

    @property
    def node_id(self) -> str:
        return self.binding.node_id


@dataclass(frozen=True, eq=False)
class CheckedPropAdmission:
    binding: PropAdmissionBinding
    context: PropAdmissionContext

    @property
    def statement(self) -> str:
        return self.binding.statement


class PropAdmissionRegistry:
    """An owner-bound registry; object identity, never record contents, authorizes.

    Only the trusted checker's conclusive-success continuation calls confirm.
    A structurally identical ticket/receipt from metadata or another registry
    cannot be consumed. Copying a registry deliberately discards all authority.
    """

    def __init__(self) -> None:
        self._graph: object | None = None
        self._owner: object | None = None
        self._supplier: Callable[[], PropAdmissionContext | None] | None = None
        self._context: PropAdmissionContext | None = None
        self._tickets: dict[str, PropCheckTicket] = {}
        self._receipts: dict[str, CheckedPropAdmission] = {}

    def __copy__(self) -> PropAdmissionRegistry:
        return type(self)()

    def __deepcopy__(self, memo: dict[int, object]) -> PropAdmissionRegistry:
        result = type(self)()
        memo[id(self)] = result
        return result

    def bind(
        self, graph: object, owner: object,
        supplier: Callable[[], PropAdmissionContext | None],
    ) -> None:
        if owner is None:
            raise ValueError("statement admission requires a live owner")
        if self._graph is not graph or self._owner is not owner:
            self._tickets.clear()
            self._receipts.clear()
            self._context = None
        self._graph, self._owner, self._supplier = graph, owner, supplier

    def owned_by(self, graph: object) -> bool:
        return self._graph is graph and self._owner is not None

    def current_context(self, graph: object) -> PropAdmissionContext | None:
        if not self.owned_by(graph) or self._supplier is None:
            return None
        try:
            context = self._supplier()
        except Exception:
            context = None
        if type(context) is not PropAdmissionContext:
            context = None
        if context is None or self._context is None or not self._context.matches(context):
            self._tickets.clear()
            self._receipts.clear()
            self._context = context
        return context

    def begin(self, graph: object, binding: PropAdmissionBinding) -> PropCheckTicket | None:
        context = self.current_context(graph)
        if context is None:
            return None
        ticket = PropCheckTicket(binding, context)
        self._tickets.pop(binding.node_id, None)
        self._tickets[binding.node_id] = ticket
        while len(self._tickets) > 64:
            self._tickets.pop(next(iter(self._tickets)))
        return ticket

    def is_current(
        self, graph: object, ticket: object, binding: PropAdmissionBinding,
    ) -> bool:
        if not isinstance(ticket, PropCheckTicket) or self._tickets.get(ticket.node_id) is not ticket:
            return False
        context = self.current_context(graph)
        return bool(
            context is not None and ticket.context.matches(context)
            and ticket.binding.matches(binding)
        )

    def discard(self, ticket: object) -> None:
        if isinstance(ticket, PropCheckTicket) and self._tickets.get(ticket.node_id) is ticket:
            self._tickets.pop(ticket.node_id, None)

    def confirm(
        self, graph: object, ticket: object, binding: PropAdmissionBinding,
    ) -> CheckedPropAdmission | None:
        if not isinstance(ticket, PropCheckTicket) or self._tickets.get(ticket.node_id) is not ticket:
            return None
        context = self.current_context(graph)
        if context is None or not ticket.context.matches(context) or not ticket.binding.matches(binding):
            return None
        self._tickets.pop(ticket.node_id, None)
        receipt = CheckedPropAdmission(binding, context)
        self._remember(receipt)
        return receipt

    def receipt(
        self, graph: object, binding: PropAdmissionBinding,
    ) -> CheckedPropAdmission | None:
        context = self.current_context(graph)
        if context is None:
            return None
        receipt = self._receipts.get(binding.node_id)
        if receipt is not None and receipt.binding.matches(binding) and receipt.context.matches(context):
            return receipt
        return None

    def authentic(
        self, graph: object, receipt: object, binding: PropAdmissionBinding,
    ) -> bool:
        if not isinstance(receipt, CheckedPropAdmission) or self._receipts.get(receipt.binding.node_id) is not receipt:
            return False
        context = self.current_context(graph)
        return bool(
            context is not None and receipt.context.matches(context)
            and receipt.binding.matches(binding)
        )

    def transfer(
        self, graph: object, receipt: CheckedPropAdmission,
        source: PropAdmissionBinding, target: PropAdmissionBinding,
    ) -> CheckedPropAdmission | None:
        if source.statement != target.statement or not self.authentic(graph, receipt, source):
            return None
        result = CheckedPropAdmission(target, receipt.context)
        self._remember(result)
        return result

    def _remember(self, receipt: CheckedPropAdmission) -> None:
        # One current capability per node bounds lookup cost. Retain a finite
        # recent working set even if a long-running graph removes old nodes.
        node_id = receipt.binding.node_id
        self._receipts.pop(node_id, None)
        self._receipts[node_id] = receipt
        while len(self._receipts) > 1024:
            self._receipts.pop(next(iter(self._receipts)))
