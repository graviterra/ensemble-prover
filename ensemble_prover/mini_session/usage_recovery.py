"""Request and physical-dispatch evidence in interrupted append-only traces."""
from __future__ import annotations

import hashlib
import json
import math
import sys
from dataclasses import dataclass, field
from typing import Any, Mapping, TypeGuard

_TOKENS = ("input_tokens", "output_tokens", "cached_input_tokens", "cache_write_tokens",
           "prompt_cache_miss_tokens", "reasoning_output_tokens")
_TERMINALS = {"llm_usage_recorded", "llm_usage_missing", "llm_late_dispatch_missing_usage",
              "llm_late_pre_generation_rejection_recorded"}


def _is_finite_number(value: Any) -> TypeGuard[int | float]:
    """Accept numbers representable as finite floats without converting large ints."""
    if isinstance(value, bool):
        return False
    if isinstance(value, int):
        return -sys.float_info.max <= value <= sys.float_info.max
    return isinstance(value, float) and math.isfinite(value)


def _identity(value: Any) -> str:
    return value if isinstance(value, str) and 0 < len(value) <= 512 else ""


def _count(value: Any) -> int:
    return sum(n for n in value.values() if type(n) is int and n > 0) if isinstance(value, dict) else 0


def _hash(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


@dataclass
class _Request:
    ids: set[str] = field(default_factory=set)
    attempts: set[str] = field(default_factory=set)
    settled: set[str] = field(default_factory=set)
    rejected: set[str] = field(default_factory=set)
    exposed: int = 0
    anonymous_settled: int = 0
    terminal: bool = False
    contribution_slots: dict[tuple[str, int], str] = field(default_factory=dict)
    dispatch_slots: dict[tuple[str, int], str] = field(default_factory=dict)
    ambiguous_slots: set[tuple[str, int]] = field(default_factory=set)
    usage_identities: set[str] = field(default_factory=set)
    unmapped_usage_identities: set[str] = field(default_factory=set)


@dataclass
class _Contribution:
    tokens: tuple[int, ...]
    complete: bool
    cost: float | None = None
    cost_complete: bool = False
    role: str = ""
    order: int = 0
    covered_attempts: frozenset[str] = frozenset()
    token_evidence: bool = True
    possible_attempts: frozenset[str] = frozenset()


@dataclass(frozen=True)
class _ScopeAmount:
    amount: int | float
    complete: bool


@dataclass(eq=False)
class _ScopeGroup:
    members: frozenset[str]
    token_adjustment: dict[str, tuple[int, ...]] = field(default_factory=dict)
    cost_adjustment: float = 0.0
    uncertain: bool = False
    conflicts: int = 0


def _scope_amounts(
    evidence: list[tuple[frozenset[str], _ScopeAmount]], *, cost: bool,
) -> tuple[list[tuple[frozenset[str], _ScopeAmount]], bool, bool]:
    """Subtract exact subsets, then choose a disjoint conservative cover.

    Non-nested overlaps without a known intersection cannot be added. Each
    candidate cover uses disjoint scopes; its sum is a lower bound. This need
    not find the tightest bound for arbitrary overlapping sets.
    """
    facts: dict[frozenset[str], _ScopeAmount] = {}
    conflict = False

    def equal(a: int | float, b: int | float) -> bool:
        return math.isclose(a, b, rel_tol=1e-9, abs_tol=1e-12) if cost else a == b

    def add(scope: frozenset[str], value: _ScopeAmount) -> None:
        nonlocal conflict
        old = facts.get(scope)
        if old is None:
            facts[scope] = value
        elif equal(old.amount, value.amount):
            facts[scope] = _ScopeAmount(min(old.amount, value.amount), old.complete or value.complete)
        elif old.complete or value.complete:
            exact = old if old.complete else value
            other = value if old.complete else old
            if other.complete or other.amount > exact.amount:
                conflict = True
            # Contradictory complete claims cannot establish an exact total.
            facts[scope] = _ScopeAmount(min(old.amount, value.amount) if other.complete
                                        else exact.amount, True)
        else:
            facts[scope] = _ScopeAmount(max(old.amount, value.amount), False)

    for scope, value in evidence:
        add(scope, value)
    universe = frozenset().union(*facts)
    # Every subtraction strictly reduces a scope, so this terminates without
    # enumerating the power set of a large multi-dispatch envelope.
    while True:
        subset = next(((small, large) for small in sorted(facts, key=lambda s: (len(s), sorted(s)))
                       if facts[small].complete for large in facts if small < large), None)
        if subset is None:
            break
        small, large = subset
        outer, inner = facts.pop(large), facts[small]
        remainder = outer.amount - inner.amount
        if remainder < 0 and not equal(outer.amount, inner.amount):
            if outer.complete:
                conflict = True
        add(large - small, _ScopeAmount(max(0, remainder), outer.complete))

    ordered = sorted(facts, key=lambda s: (-facts[s].amount, -facts[s].complete, sorted(s)))
    candidates: list[tuple[list[tuple[frozenset[str], _ScopeAmount]], int | float, bool]] = []
    for seed in ordered:
        covered: frozenset[str] = frozenset()
        chosen = []
        for scope in [seed, *ordered]:
            if not covered.intersection(scope):
                chosen.append((scope, facts[scope]))
                covered |= scope
        candidates.append((chosen, sum(value.amount for _, value in chosen),
                           covered == universe and all(value.complete for _, value in chosen)))
    exact = [candidate for candidate in candidates if candidate[2]]
    best = max(candidates, key=lambda candidate: (candidate[1], candidate[2]))
    if exact:
        authoritative = min(exact, key=lambda candidate: candidate[1])
        if not equal(best[1], authoritative[1]):
            conflict = True
        best = authoritative
    return best[0], best[2] and not conflict, conflict


def _observation_complete(observation: Mapping[str, Any], token_status: Any) -> bool:
    """Read the serialized ProviderUsageRecord schema, including token absence."""
    raw = observation.get("raw_usage", {})
    assumptions = observation.get("cost_valuation_assumptions", ())
    if (not isinstance(raw, dict) or not isinstance(assumptions, (list, tuple))
            or any(not isinstance(item, str) for item in assumptions)):
        return False
    if (raw.get("incomplete") is True
            or observation.get("usage_source") == "claude_code_subscription_partial_usage"
            or "provider_token_totals_unavailable" in assumptions
            or observation.get("token_usage_status") in ("unknown", "partial", "missing")):
        return False
    if token_status in ("unknown", "missing"):
        return False
    # A mixed envelope can contain complete individual provider receipts. Older
    # observations without the provider schema cannot establish that distinction.
    return token_status != "partial" or "raw_usage" in observation


class UsageLifecycleRecovery:
    """Reconcile receipts without inventing missing tokens or prices."""

    def __init__(self) -> None:
        self.requests: dict[str, _Request] = {}
        self.aliases: dict[str, str] = {}
        self.contributions: dict[str, _Contribution] = {}
        self.contribution_aliases: dict[str, str] = {}
        self.attempt_aliases: dict[str, str] = {}
        self.identity_missing = 0
        self.invalid_records = 0
        self.conflicting_receipts = 0
        self.token_deltas: dict[str, int] | None = None
        self.role_token_deltas: dict[str, dict[str, int]] = {}
        self.cost_delta: float | None = None
        self.reconciled = False
        self._next_contribution = 0
        self._scope_dirty: set[str] = set()
        self._scope_requests: set[str] = set()
        self._indexed_scopes: dict[str, frozenset[str]] = {}
        self._scope_index: dict[str, set[str]] = {}
        self._scope_groups: dict[str, _ScopeGroup] = {}
        self._scope_uncertain_count = 0
        self._scope_uncertain = False
        self._scope_conflicts = 0

    @staticmethod
    def _resolve(aliases: dict[str, str], identity: str) -> str:
        path = []
        while identity in aliases:
            path.append(identity)
            identity = aliases[identity]
        for alias in path:
            aliases[alias] = identity
        return identity

    def _attempts(self, attempts: set[str]) -> set[str]:
        return {self._resolve(self.attempt_aliases, attempt) for attempt in attempts}

    def _token_change(self, tokens: tuple[int, ...], role: str) -> None:
        if self.token_deltas is None:
            self.token_deltas = dict.fromkeys(_TOKENS, 0)
        role_delta = self.role_token_deltas.setdefault(role, dict.fromkeys(_TOKENS, 0))
        for name, value in zip(_TOKENS, tokens):
            self.token_deltas[name] += value
            role_delta[name] += value

    def _join_contributions(self, earlier: str, identity: str) -> str:
        """Union proven aliases and undo each formerly counted contribution.

        Physical IDs are authoritative: a local target/ordinal slot can bind an
        opaque identity to a physical one, but cannot equate two physical IDs.
        Signed deltas are generated here only, never accepted from trace JSON.
        """
        earlier = self._resolve(self.contribution_aliases, earlier)
        identity = self._resolve(self.contribution_aliases, identity)
        if earlier == identity:
            return identity
        physical = [key for key in (earlier, identity)
                    if key.startswith("attempt:physical:")]
        if len(physical) == 2:
            return identity
        root = physical[0] if physical else min(earlier, identity)
        other = identity if root == earlier else earlier
        self._scope_dirty.update((root, other))
        a, b = self.contributions.get(root), self.contributions.pop(other, None)
        self.contribution_aliases[other] = root
        if b is None:
            return root
        if a is None:
            self.contributions[root] = b
            return root
        self.reconciled = True
        # Retain first-contributor attribution even if a later envelope carries
        # the authoritative cumulative totals. Reverse the other role's charge.
        if b.order < a.order:
            a, b = b, a
        tokens, complete = a.tokens, a.complete
        if a.tokens == b.tokens:
            complete |= b.complete
        elif not a.complete and all(new >= old for old, new in zip(a.tokens, b.tokens)):
            tokens, complete = b.tokens, b.complete
        elif not b.complete and all(old >= new for old, new in zip(a.tokens, b.tokens)):
            pass
        else:
            self.conflicting_receipts += 1
        cost, cost_complete = a.cost, a.cost_complete
        if cost is None:
            cost, cost_complete = b.cost, b.cost_complete
        elif b.cost is not None:
            if cost == b.cost:
                cost_complete |= b.cost_complete
            elif not cost_complete and b.cost >= cost:
                cost, cost_complete = b.cost, b.cost_complete
            elif not b.cost_complete and cost >= b.cost:
                pass
            else:
                self.conflicting_receipts += 1
        self.contributions[root] = _Contribution(
            tokens, complete, cost, cost_complete, a.role, a.order,
            a.covered_attempts | b.covered_attempts,
            possible_attempts=a.possible_attempts | b.possible_attempts,
        )
        self._token_change(tuple(new - old for new, old in zip(tokens, a.tokens)), a.role)
        self._token_change(tuple(-value for value in b.tokens), b.role)
        if cost is not None:
            self.cost_delta = ((self.cost_delta or 0.0) + cost
                               - (a.cost or 0.0) - (b.cost or 0.0))
        return root

    def _join_attempts(self, earlier: str, attempt: str) -> str:
        earlier = self._resolve(self.attempt_aliases, earlier)
        attempt = self._resolve(self.attempt_aliases, attempt)
        if earlier == attempt:
            return attempt
        physical = [key for key in (earlier, attempt) if key.startswith("physical:")]
        if len(physical) == 2:
            return attempt
        root = physical[0] if physical else min(earlier, attempt)
        other = attempt if root == earlier else earlier
        self._scope_dirty.update(self._scope_index.get(other, ()))
        self._scope_dirty.update(self._scope_index.get(root, ()))
        self.attempt_aliases[other] = root
        self._join_contributions("attempt:" + other, "attempt:" + root)
        return root

    def observe(self, row: Mapping[str, Any], *, role: str = "") -> bool:
        duplicate = self._observe(row, role=role)
        self._reconcile_scopes()
        return duplicate

    def _contribution_scope(self, identity: str, contribution: _Contribution) -> frozenset[str]:
        scope = frozenset(self._attempts(set(contribution.covered_attempts)))
        if identity.startswith("attempt:"):
            return frozenset(self._attempts({identity.removeprefix("attempt:")}))
        if not scope and (contribution.possible_attempts or identity.startswith("observation:")):
            # An unidentified observation may overlap its request's calls, but
            # the opaque member prevents it from claiming exact coverage.
            return (frozenset(self._attempts(set(contribution.possible_attempts)))
                    | {"unmapped:" + identity})
        return scope

    def _reconcile_scopes(self) -> None:
        """Reproject only overlap components changed by this observation.

        Original evidence survives upgrades and aliases. An attempt index links
        overlapping contributions, including cost-only envelopes; disconnected
        receipts and progress events never rescan historical components.
        """
        for key in self._scope_requests:
            state = self.requests[key]
            remaining = set()
            for identity in state.unmapped_usage_identities:
                identity = self._resolve(self.contribution_aliases, identity)
                contribution = self.contributions.get(identity)
                if (contribution is not None and not contribution.covered_attempts
                        and not identity.startswith("attempt:")):
                    possible = contribution.possible_attempts | (state.attempts - state.rejected)
                    if possible != contribution.possible_attempts:
                        contribution.possible_attempts = frozenset(possible)
                        self._scope_dirty.add(identity)
                    remaining.add(identity)
            state.unmapped_usage_identities = remaining
        self._scope_requests.clear()
        dirty, self._scope_dirty = self._scope_dirty, set()
        if not dirty:
            return

        # Remove old index edges before inserting new ones, so aliases can
        # merge components and a newly exact scope can split an uncertain one.
        for identity in dirty:
            for attempt in self._indexed_scopes.pop(identity, ()):
                indexed = self._scope_index[attempt]
                indexed.remove(identity)
                if not indexed:
                    del self._scope_index[attempt]
        for identity in dirty:
            contribution = self.contributions.get(identity)
            if contribution is None:
                continue
            scope = self._contribution_scope(identity, contribution)
            if scope:
                self._indexed_scopes[identity] = scope
                for attempt in scope:
                    self._scope_index.setdefault(attempt, set()).add(identity)

        affected: set[str] = set()
        old_groups: set[_ScopeGroup] = set()
        pending = list(dirty)
        while pending:
            identity = pending.pop()
            if identity in affected:
                continue
            affected.add(identity)
            old_group = self._scope_groups.get(identity)
            if old_group is not None and old_group not in old_groups:
                old_groups.add(old_group)
                pending.extend(old_group.members)
            for attempt in self._indexed_scopes.get(identity, ()):
                pending.extend(self._scope_index[attempt] - affected)

        changes: dict[str, list[int]] = {}
        cost_change = 0.0

        def replace_projection(group: _ScopeGroup, sign: int) -> None:
            nonlocal cost_change
            for role, tokens in group.token_adjustment.items():
                delta = changes.setdefault(role, [0] * len(_TOKENS))
                for metric, value in enumerate(tokens):
                    delta[metric] += sign * value
            cost_change += sign * group.cost_adjustment
            self._scope_uncertain_count += sign * int(group.uncertain)
            self._scope_conflicts += sign * group.conflicts

        for group in old_groups:
            replace_projection(group, -1)
            for identity in group.members:
                del self._scope_groups[identity]

        remaining_ids = {identity for identity in affected if identity in self._indexed_scopes}
        while remaining_ids:
            pending = [remaining_ids.pop()]
            members = set(pending)
            while pending:
                identity = pending.pop()
                for attempt in self._indexed_scopes[identity]:
                    neighbors = self._scope_index[attempt] & remaining_ids
                    remaining_ids.difference_update(neighbors)
                    members.update(neighbors)
                    pending.extend(neighbors)
            group = self._project_scope_group(members)
            replace_projection(group, 1)
            for identity in members:
                self._scope_groups[identity] = group

        for role, delta in changes.items():
            if any(delta):
                self._token_change(tuple(delta), role)
                self.reconciled = True
        if cost_change:
            self.cost_delta = (self.cost_delta or 0.0) + cost_change
            if self.token_deltas is None:
                self.token_deltas = dict.fromkeys(_TOKENS, 0)
            self.reconciled = True
        self._scope_uncertain = self._scope_uncertain_count > 0

    def _project_scope_group(self, members: set[str]) -> _ScopeGroup:
        group = [(self._indexed_scopes[identity], self.contributions[identity])
                 for identity in members]
        adjustment: dict[str, list[int]] = {}
        cost_adjustment = 0.0
        result = _ScopeGroup(frozenset(members))
        result.uncertain = any(member.startswith("unmapped:")
                               for scope, _ in group for member in scope)
        if len(group) > 1:
            group.sort(key=lambda item: item[1].order)
            for metric in range(len(_TOKENS) + 1):
                is_cost = metric == len(_TOKENS)
                evidence = []
                for scope, contribution in group:
                    if not is_cost and not contribution.token_evidence:
                        continue
                    amount = contribution.cost if is_cost else contribution.tokens[metric]
                    if amount is not None:
                        evidence.append((scope, _ScopeAmount(
                            amount, (contribution.cost_complete if is_cost else contribution.complete)
                            and not any(member.startswith("unmapped:") for member in scope),
                        )))
                if not evidence:
                    continue
                projected, exact, conflict = _scope_amounts(evidence, cost=is_cost)
                result.conflicts += int(conflict)
                result.uncertain |= not exact
                if is_cost:
                    cost_adjustment += float(sum(value.amount for _, value in projected)
                                             - sum(value.amount for _, value in evidence))
                    continue
                for _, contribution in group:
                    if contribution.token_evidence:
                        adjustment.setdefault(contribution.role, [0] * len(_TOKENS))[metric] -= contribution.tokens[metric]
                # A scope retains its first contributing role. Exact subset
                # subtraction exposes the role shares when detailed evidence
                # arrives; earlier partial subsets retain their known minimum.
                for scope, value in projected:
                    remaining, amount = scope, int(value.amount)
                    for source, contribution in group:
                        if not contribution.token_evidence or not source & remaining:
                            continue
                        if remaining <= source:
                            share = amount
                        elif source <= remaining:
                            share = min(amount, contribution.tokens[metric])
                        else:
                            continue
                        adjustment.setdefault(contribution.role, [0] * len(_TOKENS))[metric] += share
                        amount -= share
                        remaining -= source
                        if not remaining:
                            break
                    if amount:
                        owner = next((c for s, c in group if c.token_evidence and scope <= s),
                                     next(c for s, c in group if c.token_evidence and scope & s))
                        adjustment.setdefault(owner.role, [0] * len(_TOKENS))[metric] += amount
        result.token_adjustment = {role: tuple(values) for role, values in adjustment.items()}
        result.cost_adjustment = cost_adjustment
        return result

    def _record_cost(self, previous: _Contribution, cost: Any, complete: bool) -> bool:
        if cost is None:
            return False
        self.cost_delta = self.cost_delta or 0.0
        if not _is_finite_number(cost) or cost < 0:
            self.invalid_records += 1
        elif previous.cost is None:
            self.cost_delta += cost
            previous.cost, previous.cost_complete = float(cost), complete
            return True
        elif cost == previous.cost:
            previous.cost_complete |= complete
        elif not previous.cost_complete and cost >= previous.cost:
            self.cost_delta += cost - previous.cost
            previous.cost, previous.cost_complete = float(cost), complete
            return True
        elif not complete and cost <= previous.cost:
            pass
        else:
            self.conflicting_receipts += 1
        return False

    def _observe(self, row: Mapping[str, Any], *, role: str = "") -> bool:
        """Deduplicate usage; expose per-observation token deltas to the scanner."""
        self.token_deltas = None
        self.role_token_deltas = {}
        self.cost_delta = None
        self.reconciled = False
        phase, verdict = row.get("phase"), row.get("verdict", "")
        if not isinstance(phase, str):
            self.invalid_records += 1
            return False
        if phase not in {"llm_request_prepared", "llm_provider_progress", "llm_usage"}:
            return False
        if not isinstance(verdict, str):
            self.invalid_records += 1
            return False
        aliases = [prefix + value for prefix, value in (
            ("request:", _identity(row.get("llm_request_id"))),
            ("reservation:", _identity(row.get("llm_reservation_id")))) if value]
        if not aliases:
            self.identity_missing += 1
            return False
        keys = {self.aliases[a] for a in aliases if a in self.aliases}
        key = min(keys) if keys else aliases[0]
        state = self.requests.setdefault(key, _Request())
        for other_key in keys - {key}:
            other = self.requests.pop(other_key)
            for attribute in ("ids", "attempts", "settled", "rejected", "usage_identities",
                              "unmapped_usage_identities"):
                getattr(state, attribute).update(getattr(other, attribute))
            state.exposed = max(state.exposed, other.exposed)
            state.anonymous_settled = max(state.anonymous_settled, other.anonymous_settled)
            state.terminal |= other.terminal
            state.ambiguous_slots.update(other.ambiguous_slots)
            for contribution_slot, identity in other.contribution_slots.items():
                previous_identity = state.contribution_slots.get(contribution_slot)
                state.contribution_slots[contribution_slot] = (
                    self._join_contributions(previous_identity, identity) if previous_identity else identity
                )
            for dispatch_slot, dispatch_attempt in other.dispatch_slots.items():
                previous_attempt = state.dispatch_slots.get(dispatch_slot)
                state.dispatch_slots[dispatch_slot] = (
                    self._join_attempts(previous_attempt, dispatch_attempt) if previous_attempt else dispatch_attempt
                )
                if (previous_attempt is not None
                        and self._resolve(self.attempt_aliases, previous_attempt)
                        != self._resolve(self.attempt_aliases, dispatch_attempt)):
                    state.ambiguous_slots.add(dispatch_slot)
        self._scope_requests.add(key)
        state.ids.update(aliases)
        for alias in state.ids:
            self.aliases[alias] = key
        progress = row.get("llm_provider_progress", {})
        status = progress.get("status", "") if isinstance(progress, dict) else None
        if not isinstance(status, str):
            self.invalid_records += 1
        elif phase == "llm_provider_progress" and status in {"initialized", "thinking", "responding", "finished"}:
            state.exposed = max(state.exposed, 1)

        receipts = row.get("llm_provider_dispatch_receipts", [])
        receipts = [r for r in receipts if isinstance(r, dict)] if isinstance(receipts, list) else []
        by_slot: dict[tuple[str, int], str] = {}
        by_receipt: dict[str, str] = {}
        receipt_attempts: set[str] = set()
        ambiguous_row_slots: set[tuple[str, int]] = set()
        physical_slots: dict[tuple[str, int], set[str]] = {}
        for receipt in receipts:
            target, ordinal = _identity(receipt.get("target_id")), receipt.get("dispatch_ordinal")
            physical_id = _identity(receipt.get("provider_dispatch_attempt_id"))
            if target and type(ordinal) is int and ordinal > 0 and physical_id:
                physical_slots.setdefault((target, ordinal), set()).add(physical_id)
        ambiguous_row_slots.update(slot for slot, ids in physical_slots.items() if len(ids) > 1)
        reservation = _identity(row.get("llm_reservation_id"))
        attempt: str | None
        slot: tuple[str, int] | None
        canonical_attempt_alias_count = -1
        for receipt in receipts:
            target, ordinal = _identity(receipt.get("target_id")), receipt.get("dispatch_ordinal")
            attempt = _identity(receipt.get("provider_dispatch_attempt_id"))
            attempt = "physical:" + attempt if attempt else ""
            slot = (target, ordinal) if target and type(ordinal) is int and ordinal > 0 else None
            if slot is not None:
                previous_attempt = state.dispatch_slots.get(slot)
                if not attempt:
                    attempt = previous_attempt or "slot:" + _hash([key, target, ordinal])
                elif previous_attempt is not None:
                    attempt = self._join_attempts(previous_attempt, attempt)
                    if self._resolve(self.attempt_aliases, previous_attempt) != attempt:
                        state.ambiguous_slots.add(slot)
                attempt = self._resolve(self.attempt_aliases, attempt)
                state.dispatch_slots[slot] = attempt
                previous_identity = state.contribution_slots.get(slot)
                if previous_identity is not None and slot not in ambiguous_row_slots:
                    identity = self._join_contributions(previous_identity, "attempt:" + attempt)
                    state.contribution_slots[slot] = identity
                    contribution = self.contributions.get(identity)
                    if contribution is not None and contribution.complete:
                        state.settled.add(attempt)
            else:
                attempt = self._resolve(self.attempt_aliases, attempt)
            if not attempt:
                continue
            if receipt.get("event") == "dispatch":
                # Identity enrichment is not a newly exposed dispatch.
                if canonical_attempt_alias_count != len(self.attempt_aliases):
                    state.attempts = self._attempts(state.attempts)
                    canonical_attempt_alias_count = len(self.attempt_aliases)
                if attempt not in state.attempts:
                    state.terminal = False
                state.attempts.add(attempt)
                receipt_attempts.add(attempt)
            elif receipt.get("event") == "pre_generation_rejection":
                state.rejected.add(attempt)
            if target and type(ordinal) is int and ordinal > 0:
                slot = (target, ordinal)
                if slot in by_slot and by_slot[slot] != attempt:
                    ambiguous_row_slots.add(slot)
                by_slot[slot] = attempt
                if reservation:
                    by_receipt[_hash({"reservation_id": reservation, "target_id": target,
                                      "dispatch_ordinal": ordinal})] = attempt
        for slot in ambiguous_row_slots:
            by_slot.pop(slot, None)
            by_receipt.pop(_hash({"reservation_id": reservation, "target_id": slot[0],
                                 "dispatch_ordinal": slot[1]}), None)
        state.attempts = self._attempts(state.attempts)
        state.rejected = self._attempts(state.rejected)
        state.settled = self._attempts(state.settled)
        active_attempts = state.attempts - state.rejected
        receipt_attempts = self._attempts(receipt_attempts) - state.rejected
        state.exposed = max(state.exposed, len(active_attempts), _count(row.get("provider_exposed_target_counts")))
        opaque = state.contribution_slots.get(("", 0))
        if opaque is not None and len(active_attempts) == 1 and state.exposed <= 1:
            attempt = next(iter(active_attempts))
            identity = self._join_contributions(opaque, "attempt:" + attempt)
            state.contribution_slots[("", 0)] = identity
            contribution = self.contributions.get(identity)
            if contribution is not None and contribution.complete:
                state.settled.add(attempt)
        if phase != "llm_usage" or verdict not in _TERMINALS:
            return False
        state.terminal = True
        if verdict not in {"llm_usage_recorded", "llm_usage_missing"}:
            # Other terminal rows carry lifecycle evidence only. They must not
            # seed contributions that the scanner never added to its totals.
            return False
        terminal = True
        missing = bool(row.get("usage_missing")) or verdict in {"llm_usage_missing", "llm_late_dispatch_missing_usage"}
        token_status = row.get("token_usage_status")
        known = terminal and not missing and token_status not in ("unknown", "partial", "missing")
        predispatch = row.get("status") == "pre_dispatch_failure"
        observations = row.get("provider_observations")
        observations = [o for o in observations if isinstance(o, dict)] if isinstance(observations, list) else []
        contributions: list[tuple[str, Mapping[str, Any], bool, frozenset[str]]] = []
        for observation in observations:
            target = _identity(observation.get("reservation_target_id"))
            ordinal = observation.get("reservation_dispatch_ordinal")
            attempt = (
                by_slot.get((target, ordinal)) or (
                    state.dispatch_slots.get((target, ordinal))
                    if (target, ordinal) not in state.ambiguous_slots else None
                )
            ) if type(ordinal) is int else None
            if attempt is not None:
                attempt = self._resolve(self.attempt_aliases, attempt)
            observation_known = terminal and _observation_complete(observation, token_status)
            if attempt is not None:
                identity = "attempt:" + attempt
            elif (len(active_attempts) == 1 and len(observations) == 1
                  and not target and ordinal is None and state.exposed <= 1):
                attempt = next(iter(active_attempts))
                identity = "attempt:" + attempt
            else:
                identity = "observation:" + _hash([key, target, ordinal])
                # Identity-less observations cannot resolve a multi-dispatch envelope.
            # Retain an earlier slot identity when a later row introduces the
            # physical receipt or an additional request/reservation alias.
            slot = (target, ordinal) if target and type(ordinal) is int and ordinal > 0 else None
            if slot is not None and (attempt is not None or slot not in state.ambiguous_slots):
                previous_identity = state.contribution_slots.get(slot)
                if previous_identity is not None:
                    identity = self._join_contributions(previous_identity, identity)
                state.contribution_slots[slot] = identity
            identity = self._resolve(self.contribution_aliases, identity)
            contributions.append((identity, observation, observation_known,
                                  frozenset({attempt}) if attempt else frozenset()))
        if not contributions:
            late_attempt = by_receipt.get(_identity(row.get("provider_dispatch_receipt_id")))
            covered = (frozenset({late_attempt}) if late_attempt else
                       frozenset() if row.get("late_usage") and _identity(row.get("provider_dispatch_receipt_id")) else
                       frozenset(receipt_attempts) if receipt_attempts else
                       frozenset(active_attempts) if len(active_attempts) == 1 and state.exposed <= 1 else
                       frozenset())
            identity = ("attempt:" + late_attempt if late_attempt else
                        "attempt:" + next(iter(covered)) if len(covered) == 1 else
                        "aggregate:" + _hash(sorted(covered) or [key]))
            # A single opaque observation and its later exact dispatch describe
            # the same receipt when the request supplies only one provider call.
            slot = ("", 0)
            previous_identity = (state.contribution_slots.get(slot)
                                 if len(active_attempts) <= 1 and state.exposed <= 1 else None)
            if previous_identity is not None:
                identity = self._join_contributions(previous_identity, identity)
            identity = self._resolve(self.contribution_aliases, identity)
            state.contribution_slots[slot] = identity
            contributions = [(identity, row, known, covered)]
        if self.token_deltas is None:
            self.token_deltas = {name: 0 for name in _TOKENS}
        added = False
        all_complete = True
        for identity, observation, complete, covered in contributions:
            identity = self._resolve(self.contribution_aliases, identity)
            tokens = tuple(observation.get(name, 0) for name in _TOKENS)
            if any(type(value) is not int or not _is_finite_number(value) or value < 0 for value in tokens):
                self.invalid_records += 1
                all_complete = False
                continue
            # Missing placeholders do not consume a subsequent actual receipt,
            # including an authoritative receipt that reports zero tokens.
            if missing and not any(tokens):
                all_complete = False
                continue
            state.usage_identities.add(identity)
            self._scope_dirty.add(identity)
            previous = self.contributions.get(identity)
            delta = tokens
            if previous is not None:
                delta = (0,) * len(_TOKENS)
                if previous.tokens == tokens:
                    previous.complete |= complete
                elif not previous.complete and all(new >= old for new, old in zip(tokens, previous.tokens)):
                    delta = tuple(new - old for new, old in zip(tokens, previous.tokens))
                    previous.tokens = tokens
                    previous.complete = complete
                elif not complete and all(new <= old for new, old in zip(tokens, previous.tokens)):
                    # A delayed partial snapshot cannot undo a newer receipt.
                    pass
                else:
                    self.conflicting_receipts += 1
                    all_complete = False
                    continue
                all_complete &= previous.complete
                previous.covered_attempts |= covered
                if previous.complete and not predispatch:
                    state.settled.update(covered)
            else:
                self._next_contribution += 1
                previous = self.contributions[identity] = _Contribution(
                    tokens, complete, role=role, order=self._next_contribution,
                    covered_attempts=covered,
                    possible_attempts=frozenset(active_attempts) if not covered else frozenset(),
                )
                all_complete &= complete
                if complete and not predispatch:
                    state.settled.update(covered)
                added = True
            if not previous.covered_attempts and not identity.startswith("attempt:"):
                state.unmapped_usage_identities.add(identity)
            added |= any(delta)
            self._token_change(delta, previous.role)
            cost = observation.get("cost_usd")
            if cost is None and len(contributions) == 1:
                cost = row.get("cost_usd")
            raw = observation.get("raw_usage", {})
            cost_complete = terminal and not (
                isinstance(raw, dict) and raw.get("incomplete") is True
                or observation.get("usage_source") == "claude_code_subscription_partial_usage"
            ) and (complete or observation.get("reported_cost_usd") is not None)
            added |= self._record_cost(previous, cost, cost_complete)
        if (len(observations) > 1 and row.get("cost_usd") is not None
                and any(o.get("cost_usd") is None for o in observations)):
            # Envelope-only prices cover the represented observations together;
            # they must participate in scope reconciliation too. They carry no
            # token evidence and cannot settle any additional dispatch.
            cost_scope = frozenset().union(*(scope for _, _, _, scope in contributions))
            if not all(scope for _, _, _, scope in contributions):
                cost_scope = frozenset()
            identity = "envelope-cost:" + _hash(sorted(cost_scope) or [key])
            state.usage_identities.add(identity)
            self._scope_dirty.add(identity)
            previous = self.contributions.get(identity)
            if previous is None:
                self._next_contribution += 1
                previous = self.contributions[identity] = _Contribution(
                    (0,) * len(_TOKENS), False, role=role, order=self._next_contribution,
                    covered_attempts=cost_scope, token_evidence=False,
                )
            if not previous.covered_attempts:
                state.unmapped_usage_identities.add(identity)
            added |= self._record_cost(previous, row["cost_usd"], known and all_complete)
        if known and all_complete and not predispatch and not observations:
            if not row.get("late_usage") and not active_attempts:
                # Preserve the legacy ID-less aggregate envelope convention.
                # Explicit scopes cannot settle anonymous/excess exposure.
                state.anonymous_settled = max(state.anonymous_settled, state.exposed - len(active_attempts))
        # Preserve missing-usage diagnostics; only actual duplicate receipts are suppressed.
        return not added and not missing and not predispatch

    def summary(self, *, trace_complete: bool) -> dict[str, Any]:
        states = list(self.requests.values())
        for state in states:
            for name in ("attempts", "settled", "rejected"):
                setattr(state, name, self._attempts(getattr(state, name)))
        attempts = set().union(*(s.attempts - s.rejected for s in states))
        settled = set().union(*(s.settled | s.rejected for s in states))
        def anonymous(state: _Request) -> int:
            return max(0, state.exposed - len(state.attempts))

        exposed = len(attempts) + sum(anonymous(s) for s in states)
        outstanding = len(attempts - settled) + sum(max(0, anonymous(s) - s.anonymous_settled) for s in states)
        unresolved = [s for s in states if ((s.attempts - s.rejected) - settled)
                      or anonymous(s) > s.anonymous_settled]
        no_terminal = [s for s in states if s.exposed and not s.terminal]
        prepared_only = sum(not s.exposed and not s.terminal for s in states)
        complete = (False if outstanding else None if not trace_complete or self.identity_missing
                    or self.invalid_records or self.conflicting_receipts or self._scope_conflicts
                    or self._scope_uncertain or prepared_only else True)
        return {"request_usage_complete": complete,
                "watchdog_recovery_usage_complete": complete is True,
                "dispatched_without_terminal_usage_count": len(no_terminal),
                "prepared_without_terminal_record_count": prepared_only,
                "llm_observed_provider_exposure_count": exposed,
                "llm_outstanding_provider_exposure_count": outstanding,
                "token_totals_are_lower_bound": complete is not True,
                "watchdog_recovery_unidentified_lifecycle_records": self.identity_missing,
                "watchdog_recovery_invalid_lifecycle_records": self.invalid_records,
                "watchdog_recovery_conflicting_usage_receipts": self.conflicting_receipts + self._scope_conflicts,
                "watchdog_recovery_ambiguous_usage_scopes": int(self._scope_uncertain),
                "watchdog_recovery_unsettled_request_ids": sorted(a.removeprefix("request:")
                    for s in unresolved for a in s.ids if a.startswith("request:"))[:128]}
