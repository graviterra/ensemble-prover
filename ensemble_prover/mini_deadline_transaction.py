"""Atomic proof-session state boundaries for elapsed-turn cancellation.

The tool loop can stop awaiting a cancellation-resistant coroutine.  Passing a
deadline predicate into that coroutine is necessary, but it is not sufficient:
the predicate can become true while a dossier or proof-state write is in
progress.  This module makes those writes all-or-nothing for the elapsed-turn
window. It snapshots only when a caller supplies a deadline, so ordinary
session mutations retain their zero-copy behavior.
"""

from __future__ import annotations

import copy
from contextvars import ContextVar
from typing import Any, Callable, List, Optional

from .tactic_attempt_telemetry import MONOTONIC_LEAN_ATTEMPT_METRICS


_ACTIVE_DEADLINE_TRANSACTION: ContextVar[Optional["DeadlineMutationTransaction"]] = (
    ContextVar("active_mini_deadline_transaction", default=None)
)


class DeadlineMutationTransaction:
    """Rollback Mini dossier/proof-state mutations if a deadline wins a race.

    ``ProofSearchState.checkpoint`` preserves its own graph invariants.  The
    dossier snapshot covers durable helper, scratch, attempt, metric, and root
    fields that a proof-state checkpoint intentionally leaves durable.  The
    transaction is therefore suitable for a complete tool/finalization commit,
    not merely scheduler speculation.
    """

    def __init__(
        self,
        *,
        deadline_exhausted: Optional[Callable[[], bool]],
        dossier: Any = None,
        proof_state: Any = None,
        label: str = "",
    ) -> None:
        self._deadline_exhausted = deadline_exhausted
        self._dossier = dossier
        self._proof_state = proof_state
        self._label = str(label or "deadline_mutation")
        self._dossier_snapshot: Optional[dict[str, Any]] = None
        self._proof_state_snapshot: Optional[dict[str, Any]] = None
        self._proof_state_checkpoint_id = ""
        self._proof_state_checkpoint_snapshot: Any = None
        self._participants: List[Any] = []
        self._snapshot_failed = False
        self._rolled_back = False
        self._deadline_won = False
        self._committed = False
        self._closed = False
        self._entered = False
        self._parent: Optional["DeadlineMutationTransaction"] = None
        self._context_token: Any = None
        self._nested_children: List["DeadlineMutationTransaction"] = []
        self._local_state_restored = False
        self._keep_current_state = False

    @property
    def enabled(self) -> bool:
        return bool(
            callable(self._deadline_exhausted)
            or (self._parent is not None and self._parent.enabled)
        )

    @property
    def deadline_won(self) -> bool:
        return bool(self._deadline_won)

    @property
    def committed(self) -> bool:
        """Whether the deadline-aware exit completed its durable commit."""

        return bool(self._committed)

    def deadline_elapsed(self) -> bool:
        if self._parent is not None:
            # Nested scopes share the parent's rollback/finalization point,
            # not its deadline predicate.  A helper may have a stricter local
            # limit than the enclosing tool loop, so either predicate must
            # fail closed for the whole atomic unit.
            if self._deadline_exhausted is not None:
                try:
                    expired = bool(self._deadline_exhausted())
                except Exception:
                    expired = True
                if expired:
                    self._deadline_won = True
                    return True
            return self._parent.deadline_elapsed()
        if not self.enabled:
            return False
        try:
            expired = bool(self._deadline_exhausted and self._deadline_exhausted())
        except Exception:
            expired = True
        if expired:
            self._deadline_won = True
        return expired

    def keep_current_state(self) -> bool:
        """Seal this scope's mutations without restoring the pre-entry snapshot.

        Terminal settlements (clearing a retry bit, recording a complete
        attested reject) must survive an elapsed deadline.  They are not new
        graph work; rolling them back re-arms a loop the admission already
        closed.

        Nested scopes seal themselves first.  The parent is sealed only when
        this scope shares the parent's proof-state object, because that is
        where the rollback snapshot lives.  A tool-loop parent that captured
        nothing (``proof_state=None``) must stay open so later tools can
        still mutate and so this child's ``__exit__`` cannot roll pending
        extraction back.
        """

        if self._rolled_back or self._closed:
            return False
        if self._keep_current_state and self._committed:
            return True
        self._keep_current_state = True
        if self._proof_state_checkpoint_id:
            commit = getattr(self._proof_state, "commit", None)
            if callable(commit):
                try:
                    commit(self._proof_state_checkpoint_id)
                except Exception:
                    # Keep live mutations. Returning False here would let
                    # nested __exit__ roll the tool-loop parent back and
                    # re-arm pending extraction.
                    pass
            self._proof_state_checkpoint_id = ""
        self._proof_state_snapshot = None
        self._proof_state_checkpoint_snapshot = None
        self._dossier_snapshot = None
        self._local_state_restored = True
        self._committed = True
        if (
            self._parent is not None
            and self._proof_state is not None
            and self._proof_state is self._parent._proof_state
        ):
            return self._parent.keep_current_state()
        return True

    def can_mutate(self) -> bool:
        if self._rolled_back or self._committed or self._closed:
            # Rollback is terminal for this scope.  Otherwise a caller that
            # observes a failed child transaction could append new state after
            # the snapshot had already been restored.
            return False
        if self._parent is not None:
            return (
                not self._snapshot_failed
                and not self.deadline_elapsed()
                and self._parent.can_mutate()
            )
        return not self._snapshot_failed and not self.deadline_elapsed()

    def add_participant(self, participant: Any) -> None:
        """Join a reversible external mutation to this commit boundary.

        Participants deliberately use a tiny synchronous protocol:
        ``commit()`` materializes a reversible side effect, ``finalize()``
        makes it visible, and ``rollback()`` compensates either stage.  This
        lets append-only cache publication share the same deadline decision as
        dossier and proof-state mutation without pretending it can be safely
        deep-copied.
        """

        if participant is not None:
            if self._rolled_back or self._committed or self._closed:
                # Check this scope before forwarding.  A late task can retain
                # a closed nested scope through its copied ContextVar even
                # while the live outer owner is still open.
                rollback = getattr(participant, "rollback", None)
                if callable(rollback):
                    try:
                        rollback()
                    except Exception:
                        pass
                return
            if self._parent is not None:
                # An inner tool transaction must not finalize/release a
                # cache receipt before the enclosing LLM/tool-loop boundary
                # decides whether its elapsed result wins.  Defer the receipt
                # to the outermost transaction instead.
                self._parent.add_participant(participant)
                return
            self._participants.append(participant)

    def _capture_local_state(
        self,
        *,
        capture_dossier: bool,
        capture_proof_state: bool,
    ) -> None:
        """Capture only the mutable objects this scope owns directly."""

        try:
            if capture_dossier and self._dossier is not None:
                self._dossier_snapshot = copy.deepcopy(vars(self._dossier))
            if capture_proof_state and self._proof_state is not None:
                checkpoint = getattr(self._proof_state, "checkpoint", None)
                capture = getattr(self._proof_state, "capture_checkpoint", None)
                if callable(checkpoint) and not callable(capture):
                    # Take this before opening the legacy checkpoint.  Restoring
                    # an after-checkpoint ``__dict__`` would resurrect a stale
                    # checkpoint entry after a commit-time deadline loss.
                    self._proof_state_snapshot = copy.deepcopy(vars(self._proof_state))
                if callable(checkpoint):
                    try:
                        self._proof_state_checkpoint_id = str(
                            checkpoint(dossier=self._dossier, label=self._label) or ""
                        )
                    except TypeError:
                        self._proof_state_checkpoint_id = str(
                            checkpoint(label=self._label) or ""
                        )
                if self._proof_state_checkpoint_id:
                    if callable(capture):
                        self._proof_state_checkpoint_snapshot = capture(
                            self._proof_state_checkpoint_id
                        )
                    if (
                        self._proof_state_checkpoint_snapshot is None
                        and self._proof_state_snapshot is None
                    ):
                        # Third-party/legacy states may implement only the
                        # original checkpoint/commit/rollback protocol.  Once
                        # their commit drops the checkpoint, retain a generic
                        # fallback so a deadline that flips inside commit can
                        # still restore their mutable state.
                        self._proof_state_snapshot = copy.deepcopy(
                            vars(self._proof_state)
                        )
                if not self._proof_state_checkpoint_id:
                    self._proof_state_snapshot = copy.deepcopy(vars(self._proof_state))
        except Exception:
            # Mutation with no recoverable snapshot is unsafe after a timeout.
            self._snapshot_failed = True

    def __enter__(self) -> "DeadlineMutationTransaction":
        self._entered = True
        parent = _ACTIVE_DEADLINE_TRANSACTION.get()
        if parent is not None and parent.enabled:
            # Nested Mini mutations share the outer snapshot and finalization
            # point.  Independent inner commits previously made an external
            # cache append irreversible before a later outer deadline could
            # roll back dossier/proof-state state.  A stale terminal parent
            # is also adopted deliberately: parent.can_mutate() then fails
            # closed and this child's local snapshot is restored on exit.
            self._parent = parent
            parent._nested_children.append(self)
            terminal_parent = bool(
                parent._rolled_back or parent._committed or parent._closed
            )
            # Sharing the outer commit point must not discard a child scope's
            # distinct local dossier/proof-state snapshot.  Route-local
            # dossiers are a real example: the outer owns the live state,
            # while the child mutates a shallow route copy.
            self._capture_local_state(
                capture_dossier=(
                    terminal_parent or self._dossier is not parent._dossier
                ),
                capture_proof_state=(
                    terminal_parent or self._proof_state is not parent._proof_state
                ),
            )
            self._context_token = _ACTIVE_DEADLINE_TRANSACTION.set(self)
            return self
        if not self.enabled:
            return self
        self._capture_local_state(capture_dossier=True, capture_proof_state=True)
        self._context_token = _ACTIVE_DEADLINE_TRANSACTION.set(self)
        return self

    def _restore_object_state(self, obj: Any, snapshot: Optional[dict[str, Any]]) -> None:
        if obj is None or snapshot is None:
            return
        try:
            state = vars(obj)
            state.clear()
            state.update(copy.deepcopy(snapshot))
        except Exception:
            pass

    def _restore_local_state(self, *, force: bool = False) -> None:
        # A sealed settlement must not be restored, even when a parent
        # rollback uses force=True. Reapplying the pre-entry snapshot
        # would re-arm pending residual extraction.
        if self._keep_current_state:
            return
        if self._local_state_restored and not force:
            return
        self._local_state_restored = True
        for child in reversed(self._nested_children):
            child._restore_local_state(force=force)
        monotonic_lean_metrics: dict[str, int] = {}
        current_tool_metrics = getattr(self._dossier, "tool_metrics", None)
        if isinstance(current_tool_metrics, dict):
            for key in MONOTONIC_LEAN_ATTEMPT_METRICS:
                if key not in current_tool_metrics:
                    continue
                try:
                    monotonic_lean_metrics[key] = max(
                        0,
                        int(current_tool_metrics.get(key, 0) or 0),
                    )
                except (TypeError, ValueError):
                    continue
        if self._proof_state_checkpoint_id:
            rollback = getattr(self._proof_state, "rollback", None)
            restored = False
            if callable(rollback):
                try:
                    restored = bool(rollback(self._proof_state_checkpoint_id))
                except Exception:
                    pass
            if not restored and self._proof_state_checkpoint_snapshot is not None:
                restore = getattr(self._proof_state, "restore_checkpoint", None)
                if callable(restore):
                    try:
                        restore(self._proof_state_checkpoint_snapshot)
                    except Exception:
                        pass
            if not restored:
                self._restore_object_state(
                    self._proof_state,
                    self._proof_state_snapshot,
                )
        else:
            self._restore_object_state(self._proof_state, self._proof_state_snapshot)
        # Restore after the proof-state rollback: a ProofSearchState checkpoint
        # intentionally retains durable dossier fields, while this boundary
        # must revert the entire late tool/finalization commit.
        self._restore_object_state(self._dossier, self._dossier_snapshot)
        if monotonic_lean_metrics and self._dossier is not None:
            restored_tool_metrics = getattr(self._dossier, "tool_metrics", None)
            if not isinstance(restored_tool_metrics, dict):
                restored_tool_metrics = {}
                try:
                    setattr(self._dossier, "tool_metrics", restored_tool_metrics)
                except Exception:
                    restored_tool_metrics = None
            if isinstance(restored_tool_metrics, dict):
                for key, current_value in monotonic_lean_metrics.items():
                    try:
                        restored_value = max(
                            0,
                            int(restored_tool_metrics.get(key, 0) or 0),
                        )
                    except (TypeError, ValueError):
                        restored_value = 0
                    restored_tool_metrics[key] = max(restored_value, current_value)

    def rollback(self) -> None:
        if not self.enabled:
            return
        if self._committed or (self._closed and not self._rolled_back):
            # A successful commit is terminal.  A stale child rollback must
            # never restore this owner's pre-commit snapshot over newer work.
            return
        if self._rolled_back:
            # While the owning context is still open, reapply its snapshot so
            # an ignored ``can_mutate()==False`` cannot leak a local write.
            # Once the owner has closed, rollback is terminal/idempotent:
            # reapplying an old snapshot from a late child would erase newer
            # legitimate turn state.
            if not self._closed:
                self._restore_local_state(force=True)
            return
        self._rolled_back = True
        if self._parent is not None:
            self._restore_local_state()
            self._parent.rollback()
            return
        for participant in reversed(self._participants):
            rollback = getattr(participant, "rollback", None)
            if callable(rollback):
                try:
                    rollback()
                except Exception:
                    pass
        self._restore_local_state()

    def commit(self) -> bool:
        if self._committed:
            return True
        if self._keep_current_state:
            return self.keep_current_state()
        if self._rolled_back:
            # A nested stricter deadline may already have restored the outer
            # snapshot.  Never relabel that aborted unit as committed merely
            # because the outer predicate itself has not elapsed.
            return False
        if self._parent is not None:
            if not self.can_mutate():
                self.rollback()
                return False
            if self._proof_state_checkpoint_id:
                commit = getattr(self._proof_state, "commit", None)
                if callable(commit):
                    try:
                        if not bool(commit(self._proof_state_checkpoint_id)):
                            self.rollback()
                            return False
                    except Exception:
                        self.rollback()
                        return False
            if not self.can_mutate():
                self.rollback()
                return False
            # The parent owns proof-state commit and every external receipt;
            # this inner scope is provisionally successful until that outer
            # linearization point executes.
            self._committed = True
            return True
        if not self.enabled:
            return True
        if not self.can_mutate():
            self.rollback()
            return False
        if self._proof_state_checkpoint_id:
            commit = getattr(self._proof_state, "commit", None)
            if callable(commit):
                try:
                    if not bool(commit(self._proof_state_checkpoint_id)):
                        self.rollback()
                        return False
                except Exception:
                    # A failed commit must not leave a speculative mutation.
                    self.rollback()
                    return False
        # ``ProofSearchState.commit`` discards its normal rollback snapshot.
        # Check again while this transaction still retains the captured
        # checkpoint so expiry *inside* commit remains compensatable.
        if not self.can_mutate():
            self.rollback()
            return False
        for participant in self._participants:
            commit = getattr(participant, "commit", None)
            if callable(commit):
                try:
                    if not bool(commit()):
                        self.rollback()
                        return False
                except Exception:
                    self.rollback()
                    return False
        if not self.can_mutate():
            self.rollback()
            return False
        for participant in self._participants:
            finalize = getattr(participant, "finalize", None)
            if callable(finalize):
                try:
                    if not bool(finalize()):
                        self.rollback()
                        return False
                except Exception:
                    self.rollback()
                    return False
        # A participant must remain reversible through this final gate.  Its
        # separate ``release`` step only unlocks an already sealed commit.
        # This check is the transaction's explicit linearization point: after
        # it succeeds there is no further stateful work to run, so a clock
        # tick during the non-mutating lock release does not retroactively
        # turn the already committed transaction into a late mutation.
        if not self.can_mutate():
            self.rollback()
            return False
        for participant in self._participants:
            linearize = getattr(participant, "linearize", None)
            if callable(linearize):
                try:
                    if linearize() is False:
                        self.rollback()
                        return False
                except Exception:
                    self.rollback()
                    return False
        for participant in self._participants:
            release = getattr(participant, "release", None)
            if callable(release):
                try:
                    if release() is False:
                        self.rollback()
                        return False
                except Exception:
                    self.rollback()
                    return False
        self._committed = True
        return True

    def __exit__(self, exc_type: Any, _exc: Any, _tb: Any) -> bool:
        try:
            if not self.enabled:
                return False
            if exc_type is not None or not self.commit():
                self.rollback()
        finally:
            self._closed = True
            if self._context_token is not None:
                try:
                    _ACTIVE_DEADLINE_TRANSACTION.reset(self._context_token)
                except Exception:
                    pass
        return False


def active_deadline_transaction() -> Optional[DeadlineMutationTransaction]:
    """Return the innermost open deadline transaction for this task, if any."""

    return _ACTIVE_DEADLINE_TRANSACTION.get()


__all__ = ["DeadlineMutationTransaction", "active_deadline_transaction"]
