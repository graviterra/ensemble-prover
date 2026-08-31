"""Runtime-checkable structural contracts for prover subsystem boundaries.

These protocols describe the stable interfaces used across Lean execution,
retrieval, model calls, memory, and telemetry without coupling callers to
concrete implementations.
"""

from __future__ import annotations

from pathlib import Path
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Protocol,
    Sequence,
    Tuple,
    runtime_checkable,
)

from .lean_parser import LeanParseResult


@runtime_checkable
class LeanRunnerProtocol(Protocol):
    """Contract for Lean process management and tactic oracle.

    Matches the public interface of LeanRunner as used by orchestrator.py.
    """

    project_dir: Path

    async def check(
        self,
        statement: str,
        proof_code: str,
        lemmas: List[str],
        *,
        preamble_override: str | None = None,
        timeout_s: Optional[float] = None,
        fast_fail_timeout_s: Optional[float] = None,
        max_heartbeats: Optional[int] = None,
        check_kind: str = "full",
        warning_as_error: bool = False,
        dispatch_observer: Optional[Callable[[], None]] = None,
    ) -> Any:
        """Run Lean on statement+proof and return a LeanResult."""
        ...

    async def check_with_sorry_raw(
        self,
        statement: str,
        proof_code: str,
        lemmas: List[str],
        *,
        preamble_override: str | None = None,
        timeout_s: Optional[float] = None,
        fast_fail_timeout_s: Optional[float] = None,
    ) -> tuple[LeanParseResult, str, int]:
        """Like check but with sorry, returning (parsed, raw_output, rc)."""
        ...

    async def check_term_type(
        self,
        term: str,
        *,
        preamble_override: str | None = None,
        timeout_s: float = 10.0,
    ) -> str:
        """Run ``#check`` on a declaration and return its rendered type."""
        ...

    async def apply_decl_to_goal(
        self,
        statement: str,
        decl_name: str,
        *,
        preamble_override: str | None = None,
        timeout_s: float = 10.0,
        probe_observer: Optional[Callable[[Dict[str, Any]], None]] = None,
    ) -> Dict[str, Any]:
        """Probe whether ``refine <decl_name> ?_`` fits ``statement``."""
        ...

    async def suggest_tactics(
        self,
        statement: str,
        proof_with_sorry: str,
        lemmas: List[str],
        *,
        preamble_override: str | None = None,
        commands: List[str] | Tuple[str, ...] = (),
        timeout_s: float = 60.0,
        max_heartbeats: int = 800000,
        oracle_cfg: Any = None,
        metrics_out: dict | None = None,
        max_wall_s: float = 0.0,
        goal_text: str | None = None,
        goal_hypotheses: Sequence[str] = (),
    ) -> List[str]:
        """Run Lean tactic suggestions on the first sorry hole."""
        ...


@runtime_checkable
class RetrieverProtocol(Protocol):
    """Contract for lemma retrieval subsystem.

    Matches the public interface of LemmaRetriever as used by orchestrator.py.
    """

    def retrieve(
        self,
        statement: str,
        *,
        preamble: str = "",
        domain_hint: Any = None,
        exclude: Any = None,
        exclude_sources: Any = None,
        goal_state: Optional[str] = None,
        max_results: Optional[int] = None,
    ) -> Tuple[List[Any], List[Any]]:
        """Retrieve lemmas relevant to *statement*."""
        ...

    def format_context(self, entries: List[Any]) -> str:
        """Format retrieved lemma entries as context text."""
        ...


@runtime_checkable
class LLMChatClientProtocol(Protocol):
    """Shared contract for chat-capable LLM clients used by helper layers."""

    last_truncated: bool

    async def chat(
        self,
        messages: List[Dict[str, str]],
        response_format: Optional[str] = None,
        *,
        temperature_override: Any = None,
        top_p_override: Optional[float] = None,
        max_tokens_override: Optional[int] = None,
        deadline: Optional[float] = None,
        request_timeout_override_s: Optional[float] = None,
        operation_timeout_override_s: Optional[float] = None,
        usage_callback: Optional[Any] = None,
    ) -> str:
        """Generate a single response for *messages*."""
        ...
