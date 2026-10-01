"""Host-local capacity permits for one operator coordinator.

A missing or mismatched installation is unavailable. This module does not
create a replacement ledger, does not call the network, and does not decide
token usage. Completion of a permit releases a slot only; it is not a usage
measurement.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import secrets
from typing import Any, Sequence

from .errors import LocalInferenceError
from .strictload import atomic_write_json, copy_state, durable_mutation, fingerprint, read_json_object

_MAX_BYTES = 8 * 1024 * 1024
_MAX_TIME = 10**12
_TOMBSTONES = 128
_RECORD_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$")
_OWNER = re.compile(r"^[A-Za-z_][A-Za-z0-9_-]{0,63}$")
_HEX64 = re.compile(r"^[0-9a-f]{64}$")
_SLOT = frozenset({"admitted", "dispatched", "cancel_requested", "completion_unknown"})
_TERMINAL = frozenset({"cancelled", "expired_before_dispatch", "completed", "released"})
_COMPLETABLE = frozenset({"dispatched", "cancel_requested", "completion_unknown"})
_OUTCOMES = frozenset({
    "cancelled_before_dispatch",
    "expired_before_dispatch",
    "completed",
    "capacity_released_unresolved",
    "released_by_verified_server_reset",
})
_NOTES = frozenset({
    "queue_expired", "request_expired", "heartbeat_expired", "process_stopped",
    "cancel_requested", "verified_server_reset", "operator_retain",
    "operator_release_capacity", "revalidated",
})


@dataclass(frozen=True)
class GroupDeclaration:
    name: str
    max_inflight: int
    max_queued: int
    queue_timeout_s: int
    request_timeout_s: int


@dataclass(frozen=True)
class EndpointDeclaration:
    name: str
    group: str
    max_inflight: int


class CapacityCoordinator:
    def __init__(self, directory: Path) -> None:
        self.directory = directory
        self.identity_path = directory / "identity.json"
        self.state_path = directory / "state.json"

    @classmethod
    def initialize(cls, directory: str | Path, *, installation_id: str, scope_id: str) -> "CapacityCoordinator":
        _owner(installation_id)
        _owner(scope_id)
        root = _directory(directory)
        root.mkdir(parents=True, exist_ok=True)
        with durable_mutation(root):
            coordinator = cls(root)
            identity_exists = coordinator.identity_path.exists()
            state_exists = coordinator.state_path.exists()
            if identity_exists and not state_exists:
                raise LocalInferenceError("ledger_lost")
            if state_exists and not identity_exists:
                raise LocalInferenceError("corrupt_coordinator")
            if identity_exists and state_exists:
                coordinator._load(installation_id, scope_id)
                return coordinator
            identity = {
                "schema_version": 1,
                "installation_id": installation_id,
                "scope_id": scope_id,
                "coordinator_id": secrets.token_hex(32),
            }
            atomic_write_json(coordinator.identity_path, identity, max_bytes=_MAX_BYTES)
            atomic_write_json(coordinator.state_path, _empty_state(identity), max_bytes=_MAX_BYTES)
        return cls(root)

    @classmethod
    def open(cls, directory: str | Path, *, installation_id: str, scope_id: str) -> "CapacityCoordinator":
        _owner(installation_id)
        _owner(scope_id)
        root = _directory(directory)
        if not root.is_dir():
            raise LocalInferenceError("coordinator_unavailable")
        coordinator = cls(root)
        identity_exists = coordinator.identity_path.exists()
        state_exists = coordinator.state_path.exists()
        if not identity_exists and not state_exists:
            raise LocalInferenceError("coordinator_unavailable")
        if identity_exists and not state_exists:
            raise LocalInferenceError("ledger_lost")
        if state_exists and not identity_exists:
            raise LocalInferenceError("corrupt_coordinator")
        with durable_mutation(root):
            coordinator._load(installation_id, scope_id)
        return coordinator

    def coordinator_id(self) -> str:
        return self.snapshot()["identity"]["coordinator_id"]

    def snapshot(self) -> dict[str, Any]:
        with durable_mutation(self.directory):
            return copy_state(self._load_unlocked())

    def register_declarations(
        self,
        *,
        installation_id: str,
        scope_id: str,
        groups: Sequence[GroupDeclaration],
        endpoints: Sequence[EndpointDeclaration],
    ) -> None:
        group_map, endpoint_map = _declarations(groups, endpoints)

        def apply(state: dict[str, Any]) -> None:
            _scope(state, installation_id, scope_id)
            for name, group in group_map.items():
                current = state["groups"].get(name)
                wanted = {item.name: item.max_inflight for item in endpoint_map.values() if item.group == name}
                if current is None:
                    _add_group(state, group, wanted)
                    continue
                if _policy_tuple(current) != _declared_policy(group) or {
                    key: value["max_inflight"] for key, value in current["endpoints"].items()
                } != wanted:
                    raise LocalInferenceError("policy_conflict", name)

        self._mutate(apply)

    def transition(
        self,
        group: str,
        *,
        max_inflight: int,
        max_queued: int,
        queue_timeout_s: int,
        request_timeout_s: int,
        endpoints: Sequence[EndpointDeclaration],
        operator_id: str,
        now_s: int,
    ) -> dict[str, Any]:
        _owner(group)
        _owner(operator_id)
        now = _time(now_s)
        policy = _policy_values(max_inflight, max_queued, queue_timeout_s, request_timeout_s)
        wanted: dict[str, int] = {}
        for item in endpoints:
            if type(item) is not EndpointDeclaration or item.group != group:
                raise LocalInferenceError("invalid_field", "endpoints")
            _owner(item.name)
            cap = _small(item.max_inflight, minimum=1)
            if cap > policy[0]:
                raise LocalInferenceError("endpoint_cap_exceeds_group", item.name)
            if item.name in wanted:
                raise LocalInferenceError("duplicate_declaration", item.name)
            wanted[item.name] = cap

        def apply(state: dict[str, Any]) -> dict[str, Any]:
            current = _group(state, group)
            existing = set(current["endpoints"])
            if not existing <= set(wanted):
                raise LocalInferenceError("endpoint_removal_forbidden")
            if _policy_tuple(current) == policy and {
                key: value["max_inflight"] for key, value in current["endpoints"].items()
            } == wanted:
                return _inspect(state, group)
            if len(current["transitions"]) >= 64:
                raise LocalInferenceError("transition_history_full")
            current["policy"] = {
                "max_inflight": policy[0],
                "max_queued": policy[1],
                "queue_timeout_s": policy[2],
                "request_timeout_s": policy[3],
            }
            for name, cap in wanted.items():
                current["endpoints"][name] = {"max_inflight": cap}
            current["policy_revision"] = _policy_revision(current["policy"])
            current["registration_revision"] = _registration_revision(current)
            current["transitions"].append({
                "index": len(current["transitions"]) + 1,
                "operator_id": operator_id,
                "at_s": now,
                "registration_revision": current["registration_revision"],
            })
            _touch(state, now)
            return _inspect(state, group)

        return self._mutate(apply)

    def acquire(
        self,
        *,
        group: str,
        endpoint_id: str,
        dispatch_id: str,
        owner_run: str,
        attempt_id: str,
        process_incarnation: str,
        request_fingerprint: str,
        now_s: int,
    ) -> dict[str, Any]:
        now = _time(now_s)
        self.expire_due(now)
        _ids(group, endpoint_id, dispatch_id, owner_run, attempt_id, process_incarnation, request_fingerprint)

        def apply(state: dict[str, Any]) -> dict[str, Any]:
            target = _group(state, group)
            if endpoint_id not in target["endpoints"]:
                raise LocalInferenceError("endpoint_not_registered", endpoint_id)
            existing = _find(state, dispatch_id, required=False)
            if existing is not None:
                permit, owner_group = existing
                if not _same_acquire(permit, group, endpoint_id, owner_run, attempt_id, process_incarnation, request_fingerprint):
                    raise LocalInferenceError("dispatch_conflict")
                if permit["state"] in _TERMINAL:
                    raise LocalInferenceError("dispatch_not_reusable")
                return _view(owner_group, permit)
            group_inflight, endpoint_inflight = _counts(target)
            endpoint_max = target["endpoints"][endpoint_id]["max_inflight"]
            if group_inflight < target["policy"]["max_inflight"] and endpoint_inflight[endpoint_id] < endpoint_max:
                permit = _new_permit(
                    state, target, group, endpoint_id, dispatch_id, owner_run, attempt_id,
                    process_incarnation, request_fingerprint, now, admitted=True,
                )
            elif len(target["queue"]) < target["policy"]["max_queued"]:
                permit = _new_permit(
                    state, target, group, endpoint_id, dispatch_id, owner_run, attempt_id,
                    process_incarnation, request_fingerprint, now, admitted=False,
                )
            else:
                raise LocalInferenceError("queue_overflow")
            _reindex(state)
            return _view(target, permit)

        return self._mutate(apply)

    def get_permit(self, dispatch_id: str) -> dict[str, Any]:
        state = self.snapshot()
        found = _find(state, dispatch_id, required=True)
        assert found is not None
        permit, group = found
        return _view(group, permit)

    def mark_dispatched(
        self,
        dispatch_id: str,
        *,
        owner_run: str,
        request_fingerprint: str,
        now_s: int,
        server_instance_id: str | None = None,
    ) -> dict[str, Any]:
        now = _time(now_s)
        _fingerprint(request_fingerprint)
        server = None if server_instance_id is None else _token(server_instance_id)
        self.expire_due(now)

        def apply(state: dict[str, Any]) -> dict[str, Any]:
            permit, group = _require(state, dispatch_id)
            _owner_matches(permit, owner_run)
            if permit["request_fingerprint"] != request_fingerprint:
                raise LocalInferenceError("request_binding_mismatch")
            if permit["state"] in {"dispatched", "cancel_requested", "completion_unknown"}:
                if permit["server_instance_id"] != server:
                    raise LocalInferenceError("server_instance_mismatch")
                return _view(group, permit)
            if permit["state"] != "admitted":
                raise LocalInferenceError("not_admitted")
            if permit["bound_revision"] != group["registration_revision"]:
                raise LocalInferenceError("policy_revalidation_required")
            if not _admission_fits(group, permit):
                raise LocalInferenceError("capacity_policy_conflict")
            permit["state"] = "dispatched"
            permit["was_dispatched"] = True
            permit["dispatched_at_s"] = now
            permit["server_instance_id"] = server
            permit["uncertainty"] = False
            return _view(group, permit)

        return self._mutate(apply)

    def complete(
        self,
        dispatch_id: str,
        *,
        owner_run: str,
        request_fingerprint: str,
        now_s: int,
    ) -> dict[str, Any]:
        now = _time(now_s)
        _fingerprint(request_fingerprint)

        def apply(state: dict[str, Any]) -> dict[str, Any]:
            permit, group = _require(state, dispatch_id)
            _owner_matches(permit, owner_run)
            if permit["request_fingerprint"] != request_fingerprint:
                raise LocalInferenceError("request_binding_mismatch")
            if permit["state"] not in _COMPLETABLE:
                raise LocalInferenceError("not_dispatched")
            _expire_group(group, now, skip_id=permit["permit_id"])
            permit["state"] = "completed"
            permit["outcome"] = "completed"
            permit["uncertainty"] = False
            _promote(group, now)
            _prune(group, _TOMBSTONES)
            _reindex(state)
            return _view(group, permit)

        return self._mutate(apply)

    def cancel(self, dispatch_id: str, *, owner_run: str, now_s: int) -> dict[str, Any]:
        now = _time(now_s)
        self.expire_due(now)

        def apply(state: dict[str, Any]) -> dict[str, Any]:
            permit, group = _require(state, dispatch_id)
            _owner_matches(permit, owner_run)
            if permit["state"] == "queued":
                group["queue"] = [item for item in group["queue"] if item != permit["permit_id"]]
                _cancel_before_dispatch(permit, now, "cancel_requested")
            elif permit["state"] == "admitted":
                _cancel_before_dispatch(permit, now, "cancel_requested")
            elif permit["state"] == "dispatched":
                permit["state"] = "cancel_requested"
                permit["uncertainty"] = True
                _note(permit, "cancel_requested", now)
            elif permit["state"] in {"cancel_requested", "completion_unknown", "cancelled", "expired_before_dispatch"}:
                return _view(group, permit)
            else:
                raise LocalInferenceError("permit_terminal")
            _promote(group, now)
            _prune(group, _TOMBSTONES)
            _reindex(state)
            return _view(group, permit)

        return self._mutate(apply)

    def expire_due(self, now_s: int) -> None:
        now = _time(now_s)

        def apply(state: dict[str, Any]) -> None:
            _touch(state, now)

        self._mutate(apply)

    def note_heartbeat_expired(self, dispatch_id: str, *, owner_run: str, now_s: int) -> dict[str, Any]:
        now = _time(now_s)
        self.expire_due(now)

        def apply(state: dict[str, Any]) -> dict[str, Any]:
            permit, group = _require(state, dispatch_id)
            _owner_matches(permit, owner_run)
            if permit["state"] == "dispatched":
                _become_unknown(permit, now, "heartbeat_expired")
            elif permit["state"] in {"cancel_requested", "completion_unknown"}:
                permit["heartbeat_expired"] = True
                permit["uncertainty"] = True
                _note(permit, "heartbeat_expired", now)
            elif permit["state"] in {"queued", "admitted"}:
                return _view(group, permit)
            else:
                raise LocalInferenceError("permit_terminal")
            return _view(group, permit)

        return self._mutate(apply)

    def report_process_stopped(self, process_incarnation: str, *, now_s: int) -> list[dict[str, Any]]:
        _token(process_incarnation)
        now = _time(now_s)
        self.expire_due(now)

        def apply(state: dict[str, Any]) -> list[dict[str, Any]]:
            views = []
            for group in state["groups"].values():
                for permit in list(group["permits"].values()):
                    if permit["process_incarnation"] != process_incarnation or permit["state"] in _TERMINAL:
                        continue
                    if permit["state"] == "queued":
                        group["queue"] = [item for item in group["queue"] if item != permit["permit_id"]]
                        _cancel_before_dispatch(permit, now, "process_stopped")
                    elif permit["state"] == "admitted":
                        _cancel_before_dispatch(permit, now, "process_stopped")
                    elif permit["state"] == "dispatched":
                        _become_unknown(permit, now, "process_stopped")
                    else:
                        permit["uncertainty"] = True
                        _note(permit, "process_stopped", now)
                    views.append(_view(group, permit))
            _touch(state, now)
            return views

        return self._mutate(apply)

    def verified_server_reset(
        self,
        group: str,
        *,
        previous_instance_id: str,
        new_instance_id: str,
        evidence_digest: str,
        now_s: int,
    ) -> list[dict[str, Any]]:
        _owner(group)
        _token(previous_instance_id)
        _token(new_instance_id)
        _fingerprint(evidence_digest)
        now = _time(now_s)
        if previous_instance_id == new_instance_id:
            raise LocalInferenceError("reset_evidence_rejected")

        def apply(state: dict[str, Any]) -> list[dict[str, Any]]:
            target = _group(state, group)
            released = []
            for permit in target["permits"].values():
                if (
                    permit["server_instance_id"] == previous_instance_id
                    and permit["state"] in _COMPLETABLE
                ):
                    permit["state"] = "released"
                    permit["outcome"] = "released_by_verified_server_reset"
                    permit["uncertainty"] = True
                    _note(permit, "verified_server_reset", now)
                    released.append(_view(target, permit))
            target["observed_server_instance_id"] = new_instance_id
            _promote(target, now)
            _prune(target, _TOMBSTONES)
            _reindex(state)
            return released

        return self._mutate(apply)

    def reconcile(
        self,
        dispatch_id: str,
        *,
        operator_id: str,
        decision: str,
        now_s: int,
    ) -> dict[str, Any]:
        _owner(operator_id)
        now = _time(now_s)
        if decision not in {"retain_unknown", "release_capacity_unresolved"}:
            raise LocalInferenceError("reconcile_decision_rejected")

        def apply(state: dict[str, Any]) -> dict[str, Any]:
            permit, group = _require(state, dispatch_id)
            if permit["state"] not in {"completion_unknown", "cancel_requested"}:
                raise LocalInferenceError("permit_not_unresolved")
            if decision == "retain_unknown":
                permit["uncertainty"] = True
                _note(permit, "operator_retain", now)
                return _view(group, permit)
            permit["state"] = "released"
            permit["outcome"] = "capacity_released_unresolved"
            permit["uncertainty"] = True
            _note(permit, "operator_release_capacity", now)
            _promote(group, now)
            _prune(group, _TOMBSTONES)
            _reindex(state)
            return _view(group, permit)

        return self._mutate(apply)

    def revalidate(self, dispatch_id: str, *, now_s: int) -> dict[str, Any]:
        self.expire_due(_time(now_s))

        def apply(state: dict[str, Any]) -> dict[str, Any]:
            permit, group = _require(state, dispatch_id)
            if permit["state"] in _TERMINAL:
                raise LocalInferenceError("permit_terminal")
            if permit["state"] == "admitted" and not _admission_fits(group, permit):
                raise LocalInferenceError("capacity_policy_conflict")
            if permit["bound_revision"] == group["registration_revision"]:
                return _view(group, permit)
            permit["bound_revision"] = group["registration_revision"]
            _note(permit, "revalidated", now_s)
            return _view(group, permit)

        return self._mutate(apply)

    def inspect(self, group: str) -> dict[str, Any]:
        _owner(group)
        return _inspect(self.snapshot(), group)

    def prune_terminal_tombstones(self, group: str, *, limit: int) -> int:
        _owner(group)
        if type(limit) is not int or isinstance(limit, bool) or limit < 0 or limit > _TOMBSTONES:
            raise LocalInferenceError("invalid_field", "limit")

        def apply(state: dict[str, Any]) -> int:
            target = _group(state, group)
            removed = _prune(target, limit)
            _reindex(state)
            return removed

        return self._mutate(apply)

    def _mutate(self, apply: Any) -> Any:
        with durable_mutation(self.directory):
            state = self._load_unlocked()
            working = copy_state(state)
            result = apply(working)
            working["mutation_sequence"] = state["mutation_sequence"]
            if working != state:
                working["mutation_sequence"] = state["mutation_sequence"] + 1
                _validate_state(working)
                atomic_write_json(self.state_path, working, max_bytes=_MAX_BYTES)
            return result

    def _load(self, installation_id: str, scope_id: str) -> dict[str, Any]:
        state = self._load_unlocked()
        _scope(state, installation_id, scope_id)
        return state

    def _load_unlocked(self) -> dict[str, Any]:
        if self.identity_path.is_symlink() or self.state_path.is_symlink():
            raise LocalInferenceError("symlink_forbidden")
        if not self.identity_path.is_file() or not self.state_path.is_file():
            if self.identity_path.is_file() and not self.state_path.exists():
                raise LocalInferenceError("ledger_lost")
            raise LocalInferenceError("corrupt_coordinator")
        identity = read_json_object(self.identity_path, max_bytes=_MAX_BYTES, corrupt_code="corrupt_coordinator")
        state = read_json_object(self.state_path, max_bytes=_MAX_BYTES, corrupt_code="corrupt_coordinator")
        try:
            _validate_state(state)
        except LocalInferenceError:
            raise LocalInferenceError("corrupt_coordinator") from None
        if state["identity"] != {
            "installation_id": identity.get("installation_id"),
            "scope_id": identity.get("scope_id"),
            "coordinator_id": identity.get("coordinator_id"),
        } or identity.get("schema_version") != 1:
            raise LocalInferenceError("corrupt_coordinator")
        return state


def shares_physical_scope(left: CapacityCoordinator, right: CapacityCoordinator) -> bool:
    """True only for the same persisted coordinator, not the same display names."""

    return left.coordinator_id() == right.coordinator_id()


def _empty_state(identity: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "mutation_sequence": 0,
        "identity": {
            "installation_id": identity["installation_id"],
            "scope_id": identity["scope_id"],
            "coordinator_id": identity["coordinator_id"],
        },
        "next_serial": 1,
        "dispatch_index": {},
        "groups": {},
    }


def _declarations(
    groups: Sequence[GroupDeclaration],
    endpoints: Sequence[EndpointDeclaration],
) -> tuple[dict[str, GroupDeclaration], dict[str, EndpointDeclaration]]:
    group_map: dict[str, GroupDeclaration] = {}
    endpoint_map: dict[str, EndpointDeclaration] = {}
    for item in groups:
        if type(item) is not GroupDeclaration:
            raise LocalInferenceError("invalid_field", "capacity_groups")
        _owner(item.name)
        _policy_values(item.max_inflight, item.max_queued, item.queue_timeout_s, item.request_timeout_s)
        if item.name in group_map:
            raise LocalInferenceError("duplicate_declaration", item.name)
        group_map[item.name] = item
    for endpoint in endpoints:
        if type(endpoint) is not EndpointDeclaration:
            raise LocalInferenceError("invalid_field", "endpoints")
        _owner(endpoint.name)
        _owner(endpoint.group)
        cap = _small(endpoint.max_inflight, minimum=1)
        group = group_map.get(endpoint.group)
        if group is None:
            raise LocalInferenceError("group_not_registered", endpoint.group)
        if cap > group.max_inflight:
            raise LocalInferenceError("endpoint_cap_exceeds_group", endpoint.name)
        if endpoint.name in endpoint_map:
            raise LocalInferenceError("duplicate_declaration", endpoint.name)
        endpoint_map[endpoint.name] = endpoint
    return group_map, endpoint_map


def _add_group(state: dict[str, Any], group: GroupDeclaration, endpoints: dict[str, int]) -> None:
    policy = {
        "max_inflight": group.max_inflight,
        "max_queued": group.max_queued,
        "queue_timeout_s": group.queue_timeout_s,
        "request_timeout_s": group.request_timeout_s,
    }
    record: dict[str, Any] = {
        "policy": policy,
        "policy_revision": _policy_revision(policy),
        "endpoints": {name: {"max_inflight": cap} for name, cap in endpoints.items()},
        "registration_revision": "",
        "queue": [],
        "permits": {},
        "observed_server_instance_id": None,
        "transitions": [],
    }
    record["registration_revision"] = _registration_revision(record)
    state["groups"][group.name] = record


def _new_permit(
    state: dict[str, Any],
    group: dict[str, Any],
    group_name: str,
    endpoint_id: str,
    dispatch_id: str,
    owner_run: str,
    attempt_id: str,
    process_incarnation: str,
    request_fingerprint: str,
    now: int,
    *,
    admitted: bool,
) -> dict[str, Any]:
    permit_id = "p" + secrets.token_hex(16)
    serial = state["next_serial"]
    state["next_serial"] = serial + 1
    timeout = group["policy"]["request_timeout_s"]
    queue_timeout = group["policy"]["queue_timeout_s"]
    permit = {
        "permit_id": permit_id,
        "serial": serial,
        "dispatch_id": dispatch_id,
        "group": group_name,
        "endpoint_id": endpoint_id,
        "owner_run": owner_run,
        "attempt_id": attempt_id,
        "process_incarnation": process_incarnation,
        "request_fingerprint": request_fingerprint,
        "state": "admitted" if admitted else "queued",
        "bound_revision": group["registration_revision"],
        "enqueued_at_s": now,
        "admitted_at_s": now if admitted else None,
        "dispatched_at_s": None,
        "queue_deadline_s": None if admitted else _deadline(now, queue_timeout),
        "request_deadline_s": _deadline(now, timeout) if admitted else None,
        "server_instance_id": None,
        "was_dispatched": False,
        "outcome": None,
        "uncertainty": False,
        "heartbeat_expired": False,
        "notes": [],
    }
    group["permits"][permit_id] = permit
    if not admitted:
        group["queue"].append(permit_id)
    return permit


def _touch(state: dict[str, Any], now: int) -> None:
    for group in state["groups"].values():
        _expire_group(group, now, skip_id=None)
        _promote(group, now)
        _prune(group, _TOMBSTONES)
    _reindex(state)


def _expire_group(group: dict[str, Any], now: int, *, skip_id: str | None) -> None:
    remaining = []
    for permit_id in group["queue"]:
        permit = group["permits"][permit_id]
        deadline = permit["queue_deadline_s"]
        if permit_id != skip_id and type(deadline) is int and now >= deadline:
            _cancel_before_dispatch(permit, now, "queue_expired")
        else:
            remaining.append(permit_id)
    group["queue"] = remaining
    for permit in group["permits"].values():
        if permit["permit_id"] == skip_id:
            continue
        deadline = permit["request_deadline_s"]
        if type(deadline) is not int or now < deadline:
            continue
        if permit["state"] == "admitted":
            permit["state"] = "expired_before_dispatch"
            permit["outcome"] = "expired_before_dispatch"
            permit["uncertainty"] = False
            _note(permit, "request_expired", now)
        elif permit["state"] == "dispatched":
            _become_unknown(permit, now, "request_expired")


def _promote(group: dict[str, Any], now: int) -> None:
    # Every release path uses this function, including reset/reconciliation.
    # Expired queue entries must never receive a fresh request deadline.
    _expire_group(group, now, skip_id=None)
    remaining = []
    for permit_id in group["queue"]:
        permit = group["permits"][permit_id]
        if permit["state"] != "queued":
            raise LocalInferenceError("corrupt_coordinator")
        endpoint_id = permit["endpoint_id"]
        group_inflight, endpoint_inflight = _counts(group)
        if (
            group_inflight < group["policy"]["max_inflight"]
            and endpoint_inflight[endpoint_id] < group["endpoints"][endpoint_id]["max_inflight"]
        ):
            permit["state"] = "admitted"
            permit["admitted_at_s"] = now
            permit["request_deadline_s"] = _deadline(now, group["policy"]["request_timeout_s"])
            permit["bound_revision"] = group["registration_revision"]
        else:
            remaining.append(permit_id)
    group["queue"] = remaining


def _admission_fits(group: dict[str, Any], target: dict[str, Any]) -> bool:
    """Keep existing remote work and give older admissions first revalidation.

    Lowering a cap cannot cancel already-dispatched work. Undispatched permits
    remain visible until their owners revalidate/cancel or their deadline ends;
    only the oldest reservations fitting the new caps may begin dispatch.
    """

    occupied = [
        permit for permit in group["permits"].values()
        if permit["state"] in _COMPLETABLE
        or (permit["state"] == "admitted" and permit["serial"] <= target["serial"])
    ]
    endpoint_count = sum(permit["endpoint_id"] == target["endpoint_id"] for permit in occupied)
    return (
        len(occupied) <= group["policy"]["max_inflight"]
        and endpoint_count <= group["endpoints"][target["endpoint_id"]]["max_inflight"]
    )


def _prune(group: dict[str, Any], limit: int) -> int:
    terminal = [permit for permit in group["permits"].values() if permit["state"] in _TERMINAL]
    terminal.sort(key=lambda permit: permit["serial"])
    extra = len(terminal) - limit
    if extra <= 0:
        return 0
    for permit in terminal[:extra]:
        del group["permits"][permit["permit_id"]]
    return extra


def _cancel_before_dispatch(permit: dict[str, Any], now: int, event: str) -> None:
    permit["state"] = "cancelled"
    permit["outcome"] = "cancelled_before_dispatch"
    permit["uncertainty"] = False
    _note(permit, event, now)


def _become_unknown(permit: dict[str, Any], now: int, event: str) -> None:
    permit["state"] = "completion_unknown"
    permit["uncertainty"] = True
    if event == "heartbeat_expired":
        permit["heartbeat_expired"] = True
    _note(permit, event, now)


def _note(permit: dict[str, Any], event: str, now: int) -> None:
    if event not in _NOTES:
        raise LocalInferenceError("corrupt_coordinator")
    note = {"event": event, "at_s": now}
    if permit["notes"] and permit["notes"][-1] == note:
        return
    permit["notes"].append(note)
    # Diagnostics cannot prevent completion or operator reconciliation. The
    # durable lifecycle fields above are authoritative; retain recent notes.
    del permit["notes"][:-32]


def _counts(group: dict[str, Any]) -> tuple[int, dict[str, int]]:
    endpoints = {name: 0 for name in group["endpoints"]}
    group_inflight = 0
    for permit in group["permits"].values():
        if permit["state"] in _SLOT:
            group_inflight += 1
            endpoints[permit["endpoint_id"]] += 1
    return group_inflight, endpoints


def _view(group: dict[str, Any], permit: dict[str, Any]) -> dict[str, Any]:
    return {
        "permit_id": permit["permit_id"],
        "dispatch_id": permit["dispatch_id"],
        "group": permit["group"],
        "endpoint_id": permit["endpoint_id"],
        "owner_run": permit["owner_run"],
        "state": permit["state"],
        "outcome": permit["outcome"],
        "uncertainty": permit["uncertainty"],
        "capacity_held": permit["state"] in _SLOT,
        "dispatch_started": permit["was_dispatched"],
        "completion_known": permit["state"] == "completed" or (
            permit["state"] in {"cancelled", "expired_before_dispatch"} and not permit["was_dispatched"]
        ),
        "token_usage_known": False,
        "heartbeat_expired": permit["heartbeat_expired"],
        "bound_revision": permit["bound_revision"],
        "registration_revision": group["registration_revision"],
        "revalidation_required": permit["state"] not in _TERMINAL and permit["bound_revision"] != group["registration_revision"],
        "server_instance_id": permit["server_instance_id"],
        "request_fingerprint": permit["request_fingerprint"],
        "process_incarnation": permit["process_incarnation"],
    }


def _inspect(state: dict[str, Any], group_name: str) -> dict[str, Any]:
    group = _group(state, group_name)
    group_inflight, endpoint_inflight = _counts(group)
    return {
        "group": group_name,
        "installation_id": state["identity"]["installation_id"],
        "scope_id": state["identity"]["scope_id"],
        "coordinator_id": state["identity"]["coordinator_id"],
        "policy_revision": group["policy_revision"],
        "registration_revision": group["registration_revision"],
        "max_inflight": group["policy"]["max_inflight"],
        "max_queued": group["policy"]["max_queued"],
        "queue_timeout_s": group["policy"]["queue_timeout_s"],
        "request_timeout_s": group["policy"]["request_timeout_s"],
        "occupancy": {
            "group_inflight": group_inflight,
            "queued": len(group["queue"]),
            "endpoint_inflight": endpoint_inflight,
        },
        "queue": [group["permits"][permit_id]["dispatch_id"] for permit_id in group["queue"]],
        "completion_unknown_dispatch_ids": [
            permit["dispatch_id"]
            for permit in sorted(group["permits"].values(), key=lambda item: item["serial"])
            if permit["state"] == "completion_unknown"
        ],
        "capacity_held_dispatch_ids": [
            permit["dispatch_id"]
            for permit in sorted(group["permits"].values(), key=lambda item: item["serial"])
            if permit["state"] in _SLOT
        ],
        "transition_count": len(group["transitions"]),
        "mutation_sequence": state["mutation_sequence"],
    }


def _reindex(state: dict[str, Any]) -> None:
    state["dispatch_index"] = _expected_index(state)


def _expected_index(state: dict[str, Any]) -> dict[str, dict[str, str]]:
    index: dict[str, dict[str, str]] = {}
    for group_name, group in state["groups"].items():
        queued = set()
        for permit_id in group["queue"]:
            if permit_id in queued or permit_id not in group["permits"] or group["permits"][permit_id]["state"] != "queued":
                raise LocalInferenceError("corrupt_coordinator")
            queued.add(permit_id)
        for permit_id, permit in group["permits"].items():
            if permit["state"] == "queued" and permit_id not in queued:
                raise LocalInferenceError("corrupt_coordinator")
            if permit["dispatch_id"] in index or permit["endpoint_id"] not in group["endpoints"]:
                raise LocalInferenceError("corrupt_coordinator")
            index[permit["dispatch_id"]] = {"group": group_name, "permit_id": permit_id}
    return index


def _validate_state(state: dict[str, Any]) -> None:
    try:
        _validate_state_inner(state)
    except (LocalInferenceError, KeyError, TypeError, ValueError, OverflowError):
        raise LocalInferenceError("corrupt_coordinator") from None


def _validate_state_inner(state: dict[str, Any]) -> None:
    if set(state) != {
        "schema_version", "mutation_sequence", "identity", "next_serial", "dispatch_index", "groups",
    } or type(state["schema_version"]) is not int or state["schema_version"] != 1:
        raise LocalInferenceError("corrupt_coordinator")
    identity = state["identity"]
    if set(identity) != {"installation_id", "scope_id", "coordinator_id"}:
        raise LocalInferenceError("corrupt_coordinator")
    _owner(identity["installation_id"])
    _owner(identity["scope_id"])
    _fingerprint(identity["coordinator_id"])
    if (
        type(state["mutation_sequence"]) is not int or state["mutation_sequence"] < 0
        or type(state["next_serial"]) is not int or state["next_serial"] < 1
        or type(state["groups"]) is not dict or type(state["dispatch_index"]) is not dict
    ):
        raise LocalInferenceError("corrupt_coordinator")
    serials: set[int] = set()
    for group_name, group in state["groups"].items():
        _owner(group_name)
        _validate_group(group)
        for permit_id, permit in group["permits"].items():
            if set(permit) != {
                "permit_id", "serial", "dispatch_id", "group", "endpoint_id", "owner_run",
                "attempt_id", "process_incarnation", "request_fingerprint", "state",
                "bound_revision", "enqueued_at_s", "admitted_at_s", "dispatched_at_s",
                "queue_deadline_s", "request_deadline_s", "server_instance_id",
                "was_dispatched", "outcome", "uncertainty", "heartbeat_expired", "notes",
            }:
                raise LocalInferenceError("corrupt_coordinator")
            if permit["state"] not in _SLOT | _TERMINAL | {"queued"}:
                raise LocalInferenceError("corrupt_coordinator")
            if permit["outcome"] is not None and permit["outcome"] not in _OUTCOMES:
                raise LocalInferenceError("corrupt_coordinator")
            _validate_permit(permit, permit_id, group_name)
            serial = permit["serial"]
            if type(serial) is not int or not 0 < serial < state["next_serial"] or serial in serials:
                raise LocalInferenceError("corrupt_coordinator")
            serials.add(serial)
    if state["dispatch_index"] != _expected_index(state):
        raise LocalInferenceError("corrupt_coordinator")


def _validate_group(group: dict[str, Any]) -> None:
    if type(group) is not dict or set(group) != {
        "policy", "policy_revision", "endpoints", "registration_revision", "queue",
        "permits", "observed_server_instance_id", "transitions",
    }:
        raise LocalInferenceError("corrupt_coordinator")
    policy = group["policy"]
    if type(policy) is not dict or set(policy) != {
        "max_inflight", "max_queued", "queue_timeout_s", "request_timeout_s",
    }:
        raise LocalInferenceError("corrupt_coordinator")
    _policy_values(**policy)
    if type(group["endpoints"]) is not dict or type(group["permits"]) is not dict or type(group["queue"]) is not list:
        raise LocalInferenceError("corrupt_coordinator")
    for name, endpoint in group["endpoints"].items():
        _owner(name)
        if type(endpoint) is not dict or set(endpoint) != {"max_inflight"}:
            raise LocalInferenceError("corrupt_coordinator")
        _small(endpoint["max_inflight"], minimum=1, maximum=policy["max_inflight"])
    if group["policy_revision"] != _policy_revision(policy) or group["registration_revision"] != _registration_revision(group):
        raise LocalInferenceError("corrupt_coordinator")
    if group["observed_server_instance_id"] is not None:
        _token(group["observed_server_instance_id"])
    if type(group["transitions"]) is not list or len(group["transitions"]) > 64:
        raise LocalInferenceError("corrupt_coordinator")
    for index, transition in enumerate(group["transitions"], 1):
        if type(transition) is not dict or set(transition) != {"index", "operator_id", "at_s", "registration_revision"}:
            raise LocalInferenceError("corrupt_coordinator")
        if type(transition["index"]) is not int or transition["index"] != index:
            raise LocalInferenceError("corrupt_coordinator")
        _owner(transition["operator_id"])
        _time(transition["at_s"])
        _fingerprint(transition["registration_revision"])


def _validate_permit(permit: dict[str, Any], permit_id: str, group_name: str) -> None:
    _token(permit_id)
    if permit["permit_id"] != permit_id or permit["group"] != group_name:
        raise LocalInferenceError("corrupt_coordinator")
    _ids(group_name, permit["endpoint_id"], permit["dispatch_id"], permit["owner_run"],
         permit["attempt_id"], permit["process_incarnation"], permit["request_fingerprint"])
    _fingerprint(permit["bound_revision"])
    if permit["server_instance_id"] is not None:
        _token(permit["server_instance_id"])
    for key in ("was_dispatched", "uncertainty", "heartbeat_expired"):
        if type(permit[key]) is not bool:
            raise LocalInferenceError("corrupt_coordinator")
    _time(permit["enqueued_at_s"])
    for key in ("admitted_at_s", "dispatched_at_s", "queue_deadline_s", "request_deadline_s"):
        if permit[key] is not None:
            _time(permit[key])
    started = permit["state"] in _COMPLETABLE | {"completed", "released"}
    if permit["was_dispatched"] != started or (permit["dispatched_at_s"] is not None) != started:
        raise LocalInferenceError("corrupt_coordinator")
    if (started or permit["state"] in {"admitted", "expired_before_dispatch"}) and (
        permit["admitted_at_s"] is None or permit["request_deadline_s"] is None
    ):
        raise LocalInferenceError("corrupt_coordinator")
    expected_outcomes = {
        "cancelled": {"cancelled_before_dispatch"},
        "expired_before_dispatch": {"expired_before_dispatch"},
        "completed": {"completed"},
        "released": {"capacity_released_unresolved", "released_by_verified_server_reset"},
    }
    if permit["outcome"] not in expected_outcomes.get(permit["state"], {None}):
        raise LocalInferenceError("corrupt_coordinator")
    if permit["uncertainty"] != (permit["state"] in {"cancel_requested", "completion_unknown", "released"}):
        raise LocalInferenceError("corrupt_coordinator")
    if permit["state"] == "queued" and (
        permit["admitted_at_s"] is not None or permit["request_deadline_s"] is not None or permit["queue_deadline_s"] is None
    ):
        raise LocalInferenceError("corrupt_coordinator")
    if type(permit["notes"]) is not list or len(permit["notes"]) > 32:
        raise LocalInferenceError("corrupt_coordinator")
    for note in permit["notes"]:
        if type(note) is not dict or set(note) != {"event", "at_s"} or note["event"] not in _NOTES:
            raise LocalInferenceError("corrupt_coordinator")
        _time(note["at_s"])


def _policy_revision(policy: dict[str, int]) -> str:
    return fingerprint("capacity_policy", policy)


def _registration_revision(group: dict[str, Any]) -> str:
    return fingerprint("capacity_registration", {
        "policy_revision": group["policy_revision"],
        "endpoints": {name: item["max_inflight"] for name, item in group["endpoints"].items()},
    })


def _policy_tuple(group: dict[str, Any]) -> tuple[int, int, int, int]:
    policy = group["policy"]
    return (
        policy["max_inflight"], policy["max_queued"], policy["queue_timeout_s"], policy["request_timeout_s"],
    )


def _declared_policy(group: GroupDeclaration) -> tuple[int, int, int, int]:
    return (group.max_inflight, group.max_queued, group.queue_timeout_s, group.request_timeout_s)


def _policy_values(max_inflight: int, max_queued: int, queue_timeout_s: int, request_timeout_s: int) -> tuple[int, int, int, int]:
    return (
        _small(max_inflight, minimum=1),
        _small(max_queued, minimum=0),
        _small(queue_timeout_s, minimum=1, maximum=10_000_000),
        _small(request_timeout_s, minimum=1, maximum=10_000_000),
    )


def _same_acquire(
    permit: dict[str, Any],
    group: str,
    endpoint_id: str,
    owner_run: str,
    attempt_id: str,
    process_incarnation: str,
    request_fingerprint: str,
) -> bool:
    return (
        permit["group"] == group
        and permit["endpoint_id"] == endpoint_id
        and permit["owner_run"] == owner_run
        and permit["attempt_id"] == attempt_id
        and permit["process_incarnation"] == process_incarnation
        and permit["request_fingerprint"] == request_fingerprint
    )


def _find(state: dict[str, Any], dispatch_id: str, *, required: bool) -> tuple[dict[str, Any], dict[str, Any]] | None:
    _token(dispatch_id)
    located = state["dispatch_index"].get(dispatch_id)
    if located is None:
        if required:
            raise LocalInferenceError("unknown_dispatch")
        return None
    group = state["groups"][located["group"]]
    return group["permits"][located["permit_id"]], group


def _require(state: dict[str, Any], dispatch_id: str) -> tuple[dict[str, Any], dict[str, Any]]:
    found = _find(state, dispatch_id, required=True)
    assert found is not None
    return found


def _group(state: dict[str, Any], name: str) -> dict[str, Any]:
    group = state["groups"].get(name)
    if group is None:
        raise LocalInferenceError("group_not_registered", name)
    return group


def _scope(state: dict[str, Any], installation_id: str, scope_id: str) -> None:
    identity = state["identity"]
    if identity["installation_id"] != installation_id or identity["scope_id"] != scope_id:
        raise LocalInferenceError("coordinator_scope_conflict")


def _owner_matches(permit: dict[str, Any], owner_run: str) -> None:
    _owner(owner_run)
    if permit["owner_run"] != owner_run:
        raise LocalInferenceError("owner_mismatch")


def _ids(*values: str) -> None:
    _owner(values[0])
    _owner(values[1])
    _token(values[2])
    _owner(values[3])
    _token(values[4])
    _token(values[5])
    _fingerprint(values[6])


def _deadline(now: int, timeout: int) -> int:
    if now + timeout > _MAX_TIME:
        raise LocalInferenceError("invalid_time")
    return now + timeout


def _time(value: int) -> int:
    if type(value) is not int or isinstance(value, bool) or value < 0 or value > _MAX_TIME:
        raise LocalInferenceError("invalid_time")
    return value


def _small(value: int, *, minimum: int, maximum: int = 10_000) -> int:
    if type(value) is not int or isinstance(value, bool) or value < minimum or value > maximum:
        raise LocalInferenceError("invalid_field", "max_inflight")
    return value


def _directory(value: str | Path) -> Path:
    path = Path(value)
    if path.is_symlink():
        raise LocalInferenceError("symlink_forbidden")
    return path


def _owner(value: Any) -> str:
    if type(value) is not str or _OWNER.fullmatch(value) is None:
        raise LocalInferenceError("invalid_field", "capacity_groups")
    return value


def _token(value: Any) -> str:
    if type(value) is not str or _RECORD_ID.fullmatch(value) is None:
        raise LocalInferenceError("invalid_dispatch_id")
    return value


def _fingerprint(value: Any) -> str:
    if type(value) is not str or _HEX64.fullmatch(value) is None:
        raise LocalInferenceError("invalid_request_fingerprint")
    return value
