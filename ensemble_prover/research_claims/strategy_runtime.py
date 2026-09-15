"""Task-local binding from Mini work to the durable research owner.

The context follows async children. A fork inherits data but fails the PID
check; independent child processes must use owner-mediated admission.
"""

from __future__ import annotations

import contextvars
import asyncio
from contextlib import contextmanager
from typing import Any, Iterator

from .model import json_text, object_fields, text
from .context_window import window, read_page
from .strategy import StrategyController, StrategyYield


_CURRENT: contextvars.ContextVar[StrategyRuntime | None] = contextvars.ContextVar(
    "strategy_owner", default=None
)
_SUBJECT: contextvars.ContextVar[str | None] = contextvars.ContextVar(
    "strategy_subject", default=None
)
# Strong references until cancellation-resistant transport cleanup completes.
# These tasks have no dispatch/mutation capability after the owner fences them.
_RETIRED: set[asyncio.Task[Any]] = set()


class StrategyRuntime:
    """Capabilities of one proof interval; no mathematical trust is conferred."""

    def __init__(self, controller: StrategyController, lease: dict[str, Any]):
        self.controller = controller
        self.lease = lease
        self.active = True
        self.last_attempt_id: str | None = None
        self.pending_review: dict[str, Any] | None = None
        self.late_result_handler: Any = None

    def check(self) -> None:
        if not self.active:
            raise StrategyYield(
                "closed_operation", allocation_id=self.lease["allocation_id"]
            )
        self.controller.check(self.lease)

    async def run_operation(
        self, operation: Any, *, timeout: float, on_late_result: Any = None
    ) -> Any:
        """Fence before bounded cancellation; a slow tail cannot hold research."""
        self.late_result_handler = on_late_result
        task = asyncio.create_task(operation)
        deadline = asyncio.get_running_loop().time() + timeout
        try:
            while True:
                remaining = deadline - asyncio.get_running_loop().time()
                if remaining <= 0:
                    raise TimeoutError("strategy interval expired")
                done, _ = await asyncio.wait({task}, timeout=min(0.1, remaining))
                if done:
                    # An already admitted proof result gets independent owner
                    # verification even if a simultaneous review revoked search.
                    return task.result()
                self.check()
        except BaseException:
            self.active = False
            self.controller.finish_interval(self.lease)
            task.cancel()
            done, _ = await asyncio.wait({task}, timeout=0.05)
            if done:
                self._retain_tail(task)
            else:
                _RETIRED.add(task)
                task.add_done_callback(self._retain_tail)
            raise

    def _retain_tail(self, task: asyncio.Task[Any]) -> None:
        _RETIRED.discard(task)
        try:
            result = task.result()
        except BaseException:
            return  # Consume the retired operation's exception.
        try:
            self.retain_candidate(
                json_text({"late_result": result, "trusted": False}).encode()
            )
            if self.late_result_handler is not None:
                self.late_result_handler(result)
        except Exception:
            # Candidate ingress is bounded; a closed ledger or expired ingress
            # never revives an operation or affects the current strategy.
            return

    def authorize(self, attempt_id: str) -> dict[str, Any]:
        self.check()
        # The enclosing proof operation is timed to this absolute deadline,
        # including bounded cleanup. Later nested calls receive no fresh time.
        remaining = self.lease["expires_at"] - self.controller.clock()
        receipt = self.controller.admit(
            self.lease, attempt_id, operation_seconds=max(0.001, remaining - 0.01)
        )
        self.last_attempt_id = attempt_id
        return receipt

    def register(self, statement: str, *, formal_context: str = "") -> dict[str, Any]:
        self.check()
        subject = self.controller.register_subject(
            statement,
            parent_id=_SUBJECT.get() or self.lease["subject_id"],
            formal_context=formal_context,
        )
        self.controller.attach_subject(self.lease, subject["subject_id"])
        return subject

    @contextmanager
    def subject_scope(self, subject_id: str) -> Iterator[None]:
        self.controller.subject(subject_id)
        token = _SUBJECT.set(subject_id)
        try:
            yield
        finally:
            _SUBJECT.reset(token)

    def context(self) -> dict[str, Any]:
        state = self.controller.snapshot()
        allocation = state["allocations"][self.lease["allocation_id"]]
        ids = set(allocation["subjects"])
        frontier = list(ids)
        while frontier:
            for parent in state["subjects"][frontier.pop()]["parent_ids"]:
                if parent not in ids:
                    ids.add(parent)
                    frontier.append(parent)
        return {
            "original_root": state["original_lean"]
            or state["subjects"][state["root_id"]]["statement"],
            "active_subject": _SUBJECT.get() or self.lease["subject_id"],
            "subjects": [state["subjects"][sid] for sid in sorted(ids)],
            "reviews": [
                review
                for review in state["reviews"].values()
                if review["subject_id"] in ids
            ],
            "allocation": {
                key: allocation[key]
                for key in (
                    "allocation_id",
                    "method",
                    "expires_at",
                    "requests_used",
                    "request_limit",
                )
            },
            "policy": "Question an issued ancestor or method with request_strategy_review when its quantitative target is unsupported or contradicted. This returns the attempt to research without refuting the claim or stopping the run. Useful helpers alone do not establish strategy viability.",
        }

    def read_artifact(self, payload: dict[str, Any]) -> dict[str, Any]:
        """Read an exact archived source/context page within this live interval."""
        self.check()
        object_fields(
            payload,
            {"artifact_id", "path", "offset", "length"},
            {"artifact_id"},
            "strategy artifact page",
        )
        return read_page(self.controller.store, **payload)

    def challenge(self, payload: dict[str, Any]) -> dict[str, Any]:
        self.check()
        fields = {
            "subject_handle",
            "scope",
            "argument",
            "evidence_artifact_ids",
            "remaining_uncertainty",
        }
        object_fields(
            payload, fields | {"supersedes"}, fields, "strategy review request"
        )
        issued = {subject["subject_id"] for subject in self.context()["subjects"]}
        if payload["subject_handle"] not in issued:
            raise ValueError(
                "choose a controller-issued active or ancestor subject handle"
            )
        argument = text(payload["argument"], "complete applicability argument")
        uncertainty = text(payload["remaining_uncertainty"], "remaining uncertainty")
        result = self.controller.request_review(
            payload["subject_handle"],
            scope=payload["scope"],
            method=self.lease["method"],
            argument=argument + "\nRemaining uncertainty: " + uncertainty,
            artifact_ids=payload["evidence_artifact_ids"],
            author=self.lease["consumer_id"],
            supersedes=payload.get("supersedes"),
        )
        self.pending_review = result
        return result

    def yield_requested(self) -> None:
        if self.pending_review:
            raise StrategyYield(
                "review_requested",
                subject_id=self.pending_review["subject_id"],
                allocation_id=self.lease["allocation_id"],
            )

    def retain_candidate(self, content: bytes) -> str | None:
        if self.last_attempt_id is None:
            return None
        return self.controller.receive_artifact(self.last_attempt_id, content)

    def prepare_conversation(self, conv: Any, dossier: Any = None) -> None:
        """Expose exact current/ancestor contracts at the actual model boundary."""
        statement = str(
            getattr(dossier, "root_statement", "")
            or getattr(conv, "goal_statement", "")
        ).strip()
        if statement:
            self.register(
                statement, formal_context=str(getattr(conv, "lean_preamble", "") or "")
            )
        advisory = window(self.controller.store, self.context(), limit=16000)
        advisory["retrieval_tool"] = (
            "Use read_strategy_artifact with the artifact_id, path and optional offset/length to inspect complete omitted arguments. Read them before deciding applicability."
        )
        context = json_text(advisory)
        if getattr(conv, "_strategy_context", None) != context:
            conv.ensure_bootstrap()
            # Replace the old advisory snapshot, keeping the durable owner
            # history separate from the bounded working conversation.
            conv.history[:] = [
                message
                for message in conv.history
                if not message.get("_strategy_context")
            ]
            conv.history.append(
                {
                    "role": "user",
                    "content": "Research controller context:\n" + context,
                    "_strategy_context": True,
                    "_required_prompt_context": True,
                }
            )
            conv._strategy_context = context

    def retain_dossier(self, dossier: Any) -> str | None:
        if dossier is None:
            return None
        payload = {
            "statement": getattr(dossier, "root_statement", ""),
            "candidate_proof": getattr(dossier, "final_proof", None),
            "candidate_helpers": list(dossier.verified_helper_blocks()),
            "policy": "Independently recheck exact target, assumptions and environment before acceptance",
        }
        return self.retain_candidate(json_text(payload).encode())


def current_strategy() -> StrategyRuntime | None:
    return _CURRENT.get()


def check_strategy() -> None:
    runtime = current_strategy()
    if runtime is not None:
        runtime.check()


@contextmanager
def bind_strategy(
    controller: StrategyController, lease: dict[str, Any]
) -> Iterator[StrategyRuntime]:
    runtime = StrategyRuntime(controller, lease)
    token = _CURRENT.set(runtime)
    subject_token = _SUBJECT.set(lease["subject_id"])
    try:
        yield runtime
    finally:
        runtime.active = False
        _SUBJECT.reset(subject_token)
        _CURRENT.reset(token)


REQUEST_STRATEGY_REVIEW_TOOL = {
    "type": "function",
    "function": {
        "name": "request_strategy_review",
        "description": "Return a suspect active/ancestor claim or method to independent research review. Does not refute a theorem or stop the overall run.",
        "parameters": {
            "type": "object",
            "additionalProperties": False,
            "properties": {
                "subject_handle": {"type": "string"},
                "scope": {"type": "string", "enum": sorted(StrategyController.SCOPES)},
                "argument": {"type": "string"},
                "evidence_artifact_ids": {"type": "array", "items": {"type": "string"}},
                "remaining_uncertainty": {"type": "string"},
                "supersedes": {"type": "array", "items": {"type": "string"}},
            },
            "required": [
                "subject_handle",
                "scope",
                "argument",
                "evidence_artifact_ids",
                "remaining_uncertainty",
            ],
        },
    },
}


READ_STRATEGY_ARTIFACT_TOOL = {
    "type": "function",
    "function": {
        "name": "read_strategy_artifact",
        "description": "Read an exact page of archived controller context or source evidence; omission is not negative evidence.",
        "parameters": {
            "type": "object",
            "additionalProperties": False,
            "properties": {
                "artifact_id": {"type": "string"},
                "path": {
                    "type": "array",
                    "items": {"anyOf": [{"type": "string"}, {"type": "integer"}]},
                    "maxItems": 32,
                },
                "offset": {"type": "integer", "minimum": 0},
                "length": {"type": "integer", "minimum": 1, "maximum": 12000},
            },
            "required": ["artifact_id"],
        },
    },
}
