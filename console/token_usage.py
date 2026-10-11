"""Bounded live token observations, separate from billing and estimates."""

from collections import OrderedDict
from dataclasses import dataclass, field
from typing import Any

from ensemble_prover.provider_progress import PROGRESS_KEY, progress_snapshot

FIELDS = ("input_tokens", "output_tokens", "cached_input_tokens", "cache_write_tokens", "reasoning_output_tokens")
MAX_RECEIPTS = 65536
MAX_CALLS = 64
MAX_ROLES = 32
MAX_COUNT = 2**53 - 1


def count(value: Any) -> int | None:
    return value if type(value) is int and 0 <= value <= MAX_COUNT else None


def text(value: Any, limit: int = 160) -> str:
    return value if isinstance(value, str) and len(value) <= limit and all(ord(c) >= 32 for c in value) else ""


def elapsed(value: Any) -> float | None:
    import math
    return float(value) if type(value) in (int, float) and 0 <= value <= 1e12 and math.isfinite(value) else None


def empty_totals() -> dict[str, int]:
    return {key: 0 for key in FIELDS}


@dataclass
class TokenUsageState:
    totals: dict[str, int] = field(default_factory=empty_totals)
    roles: dict[str, dict[str, int]] = field(default_factory=dict)
    observed_fields: set[str] = field(default_factory=set)
    role_fields: dict[str, set[str]] = field(default_factory=dict)
    calls: OrderedDict[str, dict[str, Any]] = field(default_factory=OrderedDict)
    seen: set[tuple[str, str]] = field(default_factory=set)
    reported_receipts: int = 0
    incomplete_receipts: int = 0
    incomplete_breakdowns: int = 0
    last_usage_s: float | None = None
    truncated: bool = False

    def consume(self, row: dict[str, Any]) -> None:
        phase = row.get("phase")
        if phase not in ("llm_request_prepared", PROGRESS_KEY, "llm_usage"):
            return
        request = text(row.get("llm_request_id"))
        role = text(row.get("role"), 80) or "llm"
        at = elapsed(row.get("elapsed_s"))
        if phase == "llm_usage":
            # This phase also carries retry-budget decisions. Those are not
            # settlements and must not retire or deduplicate the eventual usage.
            if not (any(name in row for name in FIELDS)
                    or row.get("token_usage_status") in ("reported", "partial", "unknown", "not_applicable")
                    or row.get("usage_missing") is True):
                return
            self.calls.pop(request, None)
            receipt = text(row.get("provider_dispatch_receipt_id"), 512)
            if request and (row.get("late_usage") is not True or receipt):
                key = (request, "late:" + receipt if row.get("late_usage") is True else "settled")
            elif count(row.get("turn_index")) is not None and elapsed(row.get("ts")) is not None:
                key = (request, f"trace:{row['turn_index']}:{row['ts']}")
            else:
                # Old opaque receipts need a stable trace coordinate. Without
                # either identity we cannot distinguish a replay from new usage.
                self.truncated = True
                self.incomplete_receipts += 1
                return
            if key in self.seen:
                return
            # Stop accumulating rather than silently double counting evicted IDs.
            if len(self.seen) >= MAX_RECEIPTS:
                self.truncated = True
                return
            self.seen.add(key)
            status = row.get("token_usage_status")
            if status == "not_applicable":
                return
            values = {name: count(row.get(name)) for name in FIELDS}
            available = values["input_tokens"] is not None or values["output_tokens"] is not None
            missing = (status in ("unknown", "partial") or row.get("usage_missing") is True
                       or values["input_tokens"] is None or values["output_tokens"] is None)
            if missing:
                self.incomplete_receipts += 1
            # Unknown zeros must not be advertised as reported usage. Partial
            # receipts can still contribute their observed additive counters.
            if not available or status == "unknown":
                return
            if not status and row.get("usage_missing") is True and not any(values.values()):
                return
            if any(values[name] is None for name in FIELDS[2:]):
                self.incomplete_breakdowns += 1
            if len(self.roles) >= MAX_ROLES - 1 and role not in self.roles:
                role = "other"
            totals = self.roles.setdefault(role, empty_totals())
            role_fields = self.role_fields.setdefault(role, set())
            for name, number in values.items():
                if number is None:
                    continue
                if self.totals[name] + number > MAX_COUNT:
                    self.truncated = True
                    continue
                self.totals[name] += number
                totals[name] += number
                self.observed_fields.add(name)
                role_fields.add(name)
            self.reported_receipts += 1
            if at is not None:
                self.last_usage_s = max(at, self.last_usage_s or 0)
            return
        if not request or (request, "settled") in self.seen:
            return
        previous = self.calls.get(request)
        if previous and previous["elapsedS"] is not None and (at is None or at < previous["elapsedS"]):
            return
        if phase == "llm_request_prepared":
            if previous:
                return
            envelopes = row.get("mini_request_envelopes")
            envelopes = envelopes if isinstance(envelopes, list) else []
            models = {text(e.get("model")) for e in envelopes[:32] if isinstance(e, dict)}
            model = next(iter(models)) if len(models) == 1 and len(envelopes) <= 32 and row.get("envelopes_truncated") is not True else ""
            item = {"requestId": request, "role": role, "scope": text(row.get("session_scope")),
                    "model": model, "status": "prepared", "elapsedS": at, "thinkingBlockTokens": None}
        else:
            progress = progress_snapshot(row.get(PROGRESS_KEY))
            if progress is None:
                return
            item = dict(previous or {"requestId": request, "role": role, "scope": text(row.get("session_scope")), "model": ""})
            item.update(status=progress["status"], elapsedS=at,
                        thinkingBlockTokens=count(progress.get("current_block_estimated_tokens")) if progress["status"] == "thinking" else None)
        self.calls[request] = item
        if len(self.calls) > MAX_CALLS:
            self.calls.popitem(last=False)
            self.truncated = True

    def view(self, *, partial: bool, backlog: bool) -> dict[str, Any]:
        return {"totals": {key: value if key in self.observed_fields else None for key, value in self.totals.items()} if self.reported_receipts else None,
                "roles": [{"role": role, **{key: value if key in self.role_fields[role] else None for key, value in values.items()}}
                          for role, values in self.roles.items()],
                "calls": [dict(value) for value in self.calls.values()],
                "reportedReceipts": self.reported_receipts, "incompleteReceipts": self.incomplete_receipts,
                "incompleteBreakdowns": self.incomplete_breakdowns,
                "lastUsageS": self.last_usage_s, "partial": partial or self.truncated, "backlog": backlog}
