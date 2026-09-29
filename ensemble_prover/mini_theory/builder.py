"""Model-facing candidate builder for bounded domain-theory construction."""

from __future__ import annotations

import math
import re
from dataclasses import dataclass, replace
from typing import Any, Optional, Protocol, Sequence

from ..llm_usage import call_with_optional_usage_callback, metered_or_plain_call
from ..deadline_guard import await_with_strict_deadline
from ..provider_tool_protocol import (
    mini_model_output_capacity,
    mini_reasoning_effort,
    resolve_final_no_tools_output,
)
from .model import TheoryBundleCandidate, TheoryNeed


_LEAN_FENCE_RE = re.compile(r"```(?:lean4?|Lean4?)?\s*(.*?)```", re.DOTALL)

# Domain-theory construction is a deep reasoning phase. Production defaults
# retain the model's full output capacity and do not impose a local watchdog.
_THEORY_REASONING_EFFORT = "high"
_REASONING_EFFORT_CHOICES = ("none", "minimal", "low", "medium", "high", "max", "xhigh")


class TheoryCandidateBuilder(Protocol):
    async def build(
        self,
        need: TheoryNeed,
        *,
        imports: Sequence[str],
        dependency_bundle_ids: Sequence[str],
        dependency_declarations: Sequence[str] = (),
        proof_idea_context: str = "",
        proof_idea_context_digest: str = "",
    ) -> Optional[TheoryBundleCandidate]: ...


class TheoryCandidateOutputUnavailable(RuntimeError):
    """The provider spent the completion without a usable visible answer."""

    def __init__(self, reason: str) -> None:
        self.reason = str(reason or "theory_candidate_output_unavailable")
        super().__init__(self.reason)


@dataclass
class LLMTheoryCandidateBuilder:
    """Ask one configured Mini model for a self-contained Lean theory unit."""

    client: Any
    cost_controller: Optional[Any] = None
    generated_by_model: str = ""
    generated_by_run: str = ""
    source_theorem: str = ""
    operation_timeout_s: Optional[float] = None
    reasoning_effort: str = _THEORY_REASONING_EFFORT
    max_output_tokens: Optional[int] = None

    def __post_init__(self) -> None:
        if self.operation_timeout_s is not None:
            timeout_s = float(self.operation_timeout_s)
            if not math.isfinite(timeout_s) or timeout_s <= 0.0:
                raise ValueError(
                    "operation_timeout_s must be a finite number greater than zero"
                )
            self.operation_timeout_s = timeout_s
        effort = str(self.reasoning_effort or "").strip().lower()
        if effort not in _REASONING_EFFORT_CHOICES:
            raise ValueError(
                f"reasoning_effort must be one of {_REASONING_EFFORT_CHOICES}"
            )
        self.reasoning_effort = effort
        if self.max_output_tokens is not None:
            max_tokens = int(self.max_output_tokens)
            if max_tokens <= 0:
                raise ValueError("max_output_tokens must be a positive integer")
            self.max_output_tokens = max_tokens

    def request_config(self) -> dict[str, Any]:
        """Stable request configuration without live runtime handles."""

        cfg = getattr(self.client, "cfg", None)
        client_config = {
            key: value
            for key in (
                "name",
                "base_url",
                "model",
                "temperature",
                "top_p",
                "max_tokens",
                "context_window",
                "timeout_s",
                "request_timeout_s",
                "request_timeout_disabled",
                "llm_deadline_policy",
                "reasoning_effort",
                "model_revision",
                "revision",
                "deployment_revision",
                "weights_hash",
                "model_hash",
            )
            for value in (getattr(cfg, key, None),)
            if value is not None
        }
        return {
            "schema_version": 1,
            "class": f"{type(self).__module__}.{type(self).__qualname__}",
            "client": client_config,
            "generated_by_model": str(self.generated_by_model or ""),
            "source_theorem": str(self.source_theorem or ""),
            "operation_timeout_s": (
                float(self.operation_timeout_s)
                if self.operation_timeout_s is not None
                else None
            ),
            "reasoning_effort": str(self.reasoning_effort or ""),
            "max_output_tokens": (
                int(self.max_output_tokens)
                if self.max_output_tokens is not None
                else None
            ),
        }

    def with_cost_controller(self, cost_controller: Any) -> "LLMTheoryCandidateBuilder":
        """Return a session-local meter binding without mutating this builder."""

        return replace(self, cost_controller=cost_controller)

    async def build(
        self,
        need: TheoryNeed,
        *,
        imports: Sequence[str],
        dependency_bundle_ids: Sequence[str],
        dependency_declarations: Sequence[str] = (),
        proof_idea_context: str = "",
        proof_idea_context_digest: str = "",
    ) -> Optional[TheoryBundleCandidate]:
        prompt = self._prompt(
            need,
            imports=imports,
            dependency_declarations=dependency_declarations,
        )
        conserved_context = str(proof_idea_context or "")
        if conserved_context:
            prompt = (
                f"{prompt}\n"
                "Selected proof-idea lifecycle for this consumer contract "
                "(advisory; Lean and verified theory remain authoritative):\n"
                f"{conserved_context}"
            )
        user_message: dict[str, Any] = {"role": "user", "content": prompt}
        if conserved_context:
            # The consumer contract and its lifecycle are one semantic unit.
            # Provider budget handling must omit optional material before this
            # message and fail explicitly rather than prefix-trimming either.
            user_message["pinned"] = True
            user_message["_required_prompt_context"] = {
                "kind": "theory_cognition",
                "units": [
                    "executable_consumer_contract",
                    "selected_proof_idea_lifecycle",
                ],
                "context_digest": str(proof_idea_context_digest or ""),
            }
        messages = [
            {
                "role": "system",
                "content": (
                    "You construct reusable Lean 4 mathematical domain theory. "
                    "Return only a fenced Lean block. Never use sorry, admit, "
                    "axiom, unsafe, or any problem-specific theorem/answer."
                ),
            },
            user_message,
        ]
        model_capacity = mini_model_output_capacity(self.client)
        output_tokens = (
            min(model_capacity, int(self.max_output_tokens))
            if self.max_output_tokens is not None
            else model_capacity
        )

        async def invoke_with_watchdog(usage_callback: Any) -> Any:
            call = call_with_optional_usage_callback(
                self.client.chat_raw,
                messages,
                temperature_override=0.15,
                reasoning_effort_override=mini_reasoning_effort(
                    self.client, minimum=self.reasoning_effort
                ),
                max_tokens_override=output_tokens,
                usage_callback=usage_callback,
                request_timeout_override_s=(
                    self.operation_timeout_s
                    if self.operation_timeout_s is not None
                    else float("inf")
                ),
                operation_timeout_override_s=(
                    self.operation_timeout_s
                    if self.operation_timeout_s is not None
                    else float("inf")
                ),
            )
            if self.operation_timeout_s is None:
                return await call
            return await await_with_strict_deadline(
                call,
                timeout_s=self.operation_timeout_s,
                operation_label="mini_theory_candidate_build",
                operation_ownership="result_only",
            )

        # An explicitly requested watchdog stays inside the meter so a legacy
        # adapter cannot strand the financial reservation. Production defaults
        # to the direct, unbounded branch above.
        response = await metered_or_plain_call(
            cost_controller=self.cost_controller,
            client=self.client,
            messages=messages,
            role="theory",
            scope="mini_theory",
            action_id="domain_theory_build",
            call_kind="chat_raw",
            # Size cost admission to the SAME ceiling actually sent to the
            # provider (below), so the reservation matches the real request.
            max_tokens_override=output_tokens,
            metadata={"temperature_requested": 0.15},
            invoke=invoke_with_watchdog,
        )
        content = response[0] if isinstance(response, tuple) else response
        raw_response = (
            response[1]
            if isinstance(response, tuple) and len(response) > 1
            else None
        )
        source = self._extract_source(str(content or ""))
        if not source:
            resolution = resolve_final_no_tools_output(
                content=content,
                raw_response=raw_response,
                client=self.client,
            )
            if resolution.error:
                raise TheoryCandidateOutputUnavailable(
                    resolution.event or resolution.error
                )
            return None
        return TheoryBundleCandidate.create(
            domain=need.domain,
            source=source,
            imports=imports,
            dependency_bundle_ids=dependency_bundle_ids,
            satisfies_need_ids=(need.need_id,),
            generated_by_run=self.generated_by_run,
            generated_by_model=self.generated_by_model,
            source_theorem=self.source_theorem or need.originating_root,
        )

    @staticmethod
    def _prompt(
        need: TheoryNeed,
        *,
        imports: Sequence[str],
        dependency_declarations: Sequence[str] = (),
    ) -> str:
        dependency_inventory = "\n".join(
            f"- {item}" for item in dependency_declarations
        ) or "(none)"
        return (
            "Construct the smallest reusable theory unit that satisfies this "
            "explicit consumer contract. It must compile using only the listed "
            "imports, and must be stated generically rather than in terms of the "
            "originating conjecture. Include definitions/structures/instances and "
            "bridge lemmas only when genuinely necessary.\n\n"
            f"Domain: {need.domain}\n"
            f"Need kind: {need.need_kind}\n"
            f"Mathematical need: {need.mathematical_description}\n"
            f"Consumer statement: {need.consumer_statement}\n"
            f"Required name hint: {need.required_name_hint or '(none)'}\n"
            f"Allowed imports: {', '.join(imports)}\n"
            "Verified prerequisite declarations:\n"
            f"{dependency_inventory}\n"
        )

    @staticmethod
    def _extract_source(content: str) -> str:
        matches = [match.strip() for match in _LEAN_FENCE_RE.findall(content) if match.strip()]
        if len(matches) == 1:
            return matches[0]
        return ""
