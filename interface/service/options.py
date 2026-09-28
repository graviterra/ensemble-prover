"""Bounded browser launch settings, mapped to supported mini-prover flags.

This describes explicit requests, not effective configuration. Omitted settings
remain omitted; the CLI remains responsible for its defaults and full parsing.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True)
class Option:
    key: str
    label: str
    kind: str
    group: str
    help: str
    choices: tuple[str, ...] = ()
    minimum: int = 0
    integer: bool = True
    false_flag: str | None = None

    def schema(self) -> dict[str, Any]:
        result: dict[str, Any] = {
            "key": self.key, "label": self.label, "kind": self.kind,
            "group": self.group, "help": self.help,
        }
        if self.choices:
            result["choices"] = list(self.choices)
        if self.kind == "number":
            result.update({"min": self.minimum, "step": 1 if self.integer else "any"})
        return result


_MODES = ("provider-default", "auto", "on", "off")
_EFFORTS = ("none", "low", "medium", "high", "max")
_FIELDS = (
    Option("mini-recursive-passes", "Recursive passes", "number", "Search",
           "Recursive plan, prove and integrate passes. Zero uses the CLI default; it does not disable recursion."),
    Option("mini-recursive-claims", "Recursive claims", "number", "Search",
           "Maximum helper and root claims across planner tranches. Zero uses the CLI default."),
    Option("mini-recursive-turns-per-claim", "Turns per recursive claim", "number", "Search",
           "Prover and refiner turns allocated to each helper goal. Zero uses the CLI default."),
    Option("max-tool-calls-per-turn", "Tool calls per turn", "number", "Search",
           "Cap on tool calls within one conversational turn; not a run-wide call budget."),
    Option("root-tactic-prepass", "Root tactic prepass", "boolean", "Search",
           "Run the deterministic root-close portfolio before the first model proof attempt.",
           false_flag="--no-root-tactic-prepass"),
    Option("startup-root-fast-lane", "Startup root fast lane", "boolean", "Search",
           "Run a bounded deterministic root-close attempt before decomposition.",
           false_flag="--no-startup-root-fast-lane"),
    Option("mini-theory-promote-verified-helpers", "Promote verified helpers", "boolean", "Search",
           "Stage generic verified helpers for independent compilation and publication after the worker exits. Disabled omits this opt-in flag."),
    Option("reasoning-mode", "Global reasoning mode", "select", "Reasoning",
           "Provider default sends no explicit reasoning control. On and off are explicit requests. Auto is an alias for provider-default.", _MODES),
    Option("reasoning-effort", "Global reasoning effort", "select", "Reasoning",
           "Effort is separate from reasoning mode. None explicitly disables reasoning where supported.", _EFFORTS),
    Option("prover-reasoning-mode", "Prover reasoning mode", "select", "Reasoning",
           "Override global reasoning mode for the prover.", _MODES),
    Option("prover-reasoning-effort", "Prover reasoning effort", "select", "Reasoning",
           "Override global reasoning effort for the prover.", _EFFORTS),
    Option("refiner-reasoning-mode", "Refiner reasoning mode", "select", "Reasoning",
           "Override global reasoning mode for the refiner.", _MODES),
    Option("refiner-reasoning-effort", "Refiner reasoning effort", "select", "Reasoning",
           "Override global reasoning effort for the refiner.", _EFFORTS),
    Option("max-prove-turns", "Prove turn cap", "number", "Budgets",
           "Maximum direct prover conversation turns. Zero disables direct prover turns."),
    Option("max-refine-turns", "Refine turn cap", "number", "Budgets",
           "Maximum refiner conversation turns. Zero disables refiner turns."),
    Option("cost-budget-usd", "Cost budget (USD)", "number", "Budgets",
           "Zero disables dollar-budget stops; available usage and cost are still recorded.", integer=False),
    Option("mini-run-wall-clock-budget-s", "Run wall-clock budget (seconds)", "number", "Budgets",
           "Cumulative run governor. Zero disables this clock; it does not disable other limits.", integer=False),
    Option("lean-timeout-s", "Lean timeout (seconds)", "number", "Budgets",
           "Positive wall-clock cap for each Lean check.", minimum=1),
    Option("llm-deadline-policy", "LLM deadline policy", "select", "Budgets",
           "Soft waits across local phase deadlines. Hard bounds an individual model/tool operation.", ("soft", "hard")),
)
_BY_KEY = {field.key: field for field in _FIELDS}


class OptionValidationError(ValueError):
    """A setting failure whose browser text uses only trusted schema metadata."""

    def __init__(self, code: str, *, key: str = "", role: str = "") -> None:
        self.code = code
        self.key = key
        self.role = role
        super().__init__(self.public_message)

    @property
    def public_message(self) -> str:
        if self.code == "object":
            return "options must be an object"
        if self.code == "unsupported":
            return "unsupported option; choose a setting from the available options"
        if self.role in ("prover", "refiner"):
            role = "prover" if self.role == "prover" else "refiner"
            if self.code == "reasoning_off":
                return f"{role} reasoning mode off requires reasoning effort none or an omitted effort"
            if self.code == "reasoning_on":
                return f"{role} reasoning mode on cannot be combined with reasoning effort none"
        field = _BY_KEY.get(self.key)
        if field is not None:
            if self.code == "boolean":
                return f"{field.key} must be true or false"
            if self.code == "select":
                return f"{field.key} must be one of: {', '.join(field.choices)}"
            if self.code == "number":
                return f"{field.key} must be a finite number of at least {field.minimum}"
            if self.code == "integer":
                return f"{field.key} must be a whole number"
        return "Invalid launch options. Choose settings from the available options."


def option_schema() -> dict[str, list[dict[str, Any]]]:
    """Metadata only: no project or provider execution."""
    return {"fields": [field.schema() for field in _FIELDS]}


def _validate_reasoning(options: dict[str, Any], *, refiner_enabled: bool) -> None:
    """Check effective active-role settings using the CLI inheritance rules."""
    for role in ("prover", "refiner") if refiner_enabled else ("prover",):
        mode = options.get(f"{role}-reasoning-mode", options.get("reasoning-mode", "provider-default"))
        effort = options.get(f"{role}-reasoning-effort", options.get("reasoning-effort"))
        if mode == "off" and effort not in (None, "none"):
            raise OptionValidationError("reasoning_off", role=role)
        if mode == "on" and effort == "none":
            raise OptionValidationError("reasoning_on", role=role)


def option_args(
    options: Any, *, refiner_enabled: bool = False, proof_search: bool = True,
) -> list[str]:
    """Validate typed settings and return only allowlisted argument tokens."""
    if not isinstance(options, dict):
        raise OptionValidationError("object")
    for key in options:
        if key not in _BY_KEY:
            raise OptionValidationError("unsupported")
    args: list[str] = []
    for field in _FIELDS:
        if field.key not in options:
            continue
        value = options[field.key]
        flag = f"--{field.key}"
        if field.kind == "boolean":
            if not isinstance(value, bool):
                raise OptionValidationError("boolean", key=field.key)
            if value:
                args.append(flag)
            elif field.false_flag:
                args.append(field.false_flag)
        elif field.kind == "select":
            if not isinstance(value, str) or value not in field.choices:
                raise OptionValidationError("select", key=field.key)
            args.extend([flag, value])
        else:
            try:
                finite = not isinstance(value, bool) and isinstance(value, (int, float)) and math.isfinite(value)
            except OverflowError:
                finite = False
            if not finite or value < field.minimum:
                raise OptionValidationError("number", key=field.key)
            if field.integer and int(value) != value:
                raise OptionValidationError("integer", key=field.key)
            args.extend([flag, str(int(value) if field.integer else value)])
    if proof_search:
        _validate_reasoning(options, refiner_enabled=refiner_enabled)
    return args
