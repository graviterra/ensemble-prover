"""Run-owned local compute allocation, conserved across children and resume.

Counts dispatches, admitted output-token envelopes, and the sum of
client-observed request wall time. It does not price API dollars or record
provider token usage. Opening a saved ledger never refills it.
"""

from __future__ import annotations

from pathlib import Path
import re
from typing import Any

from .errors import LocalInferenceError
from .strictload import atomic_write_json, copy_state, durable_mutation, read_json_object

_MAX_BYTES = 8 * 1024 * 1024
_MAX_COUNT = 10_000_000
_MAX_WALL_MS = 1_000_000_000 * 1000
_RECORD_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$")
_OWNER = re.compile(r"^[A-Za-z_][A-Za-z0-9_-]{0,63}$")


class LocalComputeLedger:
    """Durable parent allocation. A child debits this object and does not copy it."""

    def __init__(self, directory: Path) -> None:
        self.directory = directory
        self.path = directory / "ledger.json"

    @classmethod
    def create(
        cls,
        directory: str | Path,
        *,
        ledger_id: str,
        profile_hash: str,
        max_dispatches: int,
        max_requested_output_tokens: int,
        max_observed_request_wall_s: int,
    ) -> "LocalComputeLedger":
        root = _directory(directory)
        _hex(ledger_id, 32)
        _hex(profile_hash, 64)
        dispatches = _count(max_dispatches, minimum=1)
        output = _count(max_requested_output_tokens, minimum=1)
        wall_s = _count(max_observed_request_wall_s, minimum=1, maximum=1_000_000_000)
        state = {
            "schema_version": 2,
            "ledger_id": ledger_id,
            "mutation_sequence": 0,
            "segments": [{"index": 0, "profile_hash": profile_hash, "reason": "create"}],
            "ceilings": {
                "dispatches": dispatches,
                "requested_output_tokens": output,
                "observed_request_wall_ms": wall_s * 1000,
            },
            "consumed": {"dispatches": 0, "requested_output_tokens": 0, "observed_request_wall_ms": 0},
            "reserved": {"dispatches": 0, "requested_output_tokens": 0, "observed_request_wall_ms": 0},
            "extensions": [],
            "reservations": {},
        }
        _validate(state)
        root.mkdir(parents=True, exist_ok=True)
        with durable_mutation(root):
            if (root / "ledger.json").exists() or (root / "ledger.json").is_symlink():
                raise LocalInferenceError("budget_exists")
            atomic_write_json(root / "ledger.json", state, max_bytes=_MAX_BYTES)
        return cls(root)

    @classmethod
    def open(cls, directory: str | Path) -> "LocalComputeLedger":
        root = _directory(directory)
        path = root / "ledger.json"
        if root.is_symlink() or not path.is_file():
            raise LocalInferenceError("budget_unavailable")
        with durable_mutation(root):
            _validate(read_json_object(path, max_bytes=_MAX_BYTES, corrupt_code="corrupt_ledger"))
        return cls(root)

    def client(self, owner: str) -> "LocalComputeClient":
        _owner(owner)
        return LocalComputeClient(self, owner)

    def snapshot(self) -> dict[str, Any]:
        with durable_mutation(self.directory):
            return copy_state(self._load())

    @property
    def active_profile_hash(self) -> str:
        return self.snapshot()["segments"][-1]["profile_hash"]

    def has_unreserved_remainder(self) -> bool:
        state = self.snapshot()
        dispatch_left = state["ceilings"]["dispatches"] - state["consumed"]["dispatches"] - state["reserved"]["dispatches"]
        output_left = (
            state["ceilings"]["requested_output_tokens"]
            - state["consumed"]["requested_output_tokens"]
            - state["reserved"]["requested_output_tokens"]
        )
        wall_left = _wall_remaining(state)
        return dispatch_left > 0 and output_left > 0 and wall_left > 0

    def reservation(self, dispatch_id: str) -> dict[str, Any]:
        _token(dispatch_id)
        state = self.snapshot()
        item = state["reservations"].get(dispatch_id)
        if item is None:
            raise LocalInferenceError("unknown_reservation")
        return _view(item)

    def reserve(
        self,
        *,
        dispatch_id: str,
        requested_output_tokens: int,
        requested_wall_ms: int,
        units: int = 1,
        owner: str,
        expected_profile_hash: str | None = None,
    ) -> dict[str, Any]:
        _token(dispatch_id)
        _owner(owner)
        per_unit = _count(requested_output_tokens, minimum=1)
        count = _count(units, minimum=1, maximum=10_000)
        wall_per_unit = _count(requested_wall_ms, minimum=1, maximum=_MAX_WALL_MS)
        if expected_profile_hash is not None:
            _hex(expected_profile_hash, 64)
        total = per_unit * count
        if total > _MAX_COUNT:
            raise LocalInferenceError("allocation_exhausted", "output_tokens")

        def apply(state: dict[str, Any]) -> dict[str, Any]:
            if expected_profile_hash is not None and state["segments"][-1]["profile_hash"] != expected_profile_hash:
                raise LocalInferenceError("profile_hash_mismatch")
            current = state["reservations"].get(dispatch_id)
            if current is not None:
                if (
                    current["owner"] != owner
                    or current["units"] != count
                    or current["requested_output_tokens_per_unit"] != per_unit
                    or current["requested_wall_ms_per_unit"] != wall_per_unit
                ):
                    raise LocalInferenceError("dispatch_conflict")
                if current["state"] == "reserved":
                    return _view(current)
                raise LocalInferenceError("dispatch_not_reusable")
            _require_room(state, dispatches=count, output_tokens=total)
            granted_per_unit = min(wall_per_unit, _wall_remaining(state) // count)
            if granted_per_unit <= 0:
                raise LocalInferenceError("allocation_exhausted", "wall")
            wall_envelope = granted_per_unit * count
            state["reserved"]["dispatches"] += count
            state["reserved"]["requested_output_tokens"] += total
            state["reserved"]["observed_request_wall_ms"] += wall_envelope
            state["reservations"][dispatch_id] = {
                "dispatch_id": dispatch_id,
                "owner": owner,
                "units": count,
                "requested_output_tokens_per_unit": per_unit,
                "requested_output_tokens": total,
                "profile_hash": state["segments"][-1]["profile_hash"],
                "requested_wall_ms_per_unit": wall_per_unit,
                "granted_wall_ms": granted_per_unit,
                "wall_envelope_ms": wall_envelope,
                "wall_reserved_ms": wall_envelope,
                "state": "reserved",
                "wall_ms": 0,
                "wall_receipt": None,
                "wall_final": False,
                "unresolved_operator": None,
            }
            return _view(state["reservations"][dispatch_id])

        return self._mutate(apply)

    def release_not_dispatched(self, dispatch_id: str, *, owner: str) -> dict[str, Any]:
        def apply(state: dict[str, Any]) -> dict[str, Any]:
            item = _owned(state, dispatch_id, owner)
            if item["state"] != "reserved":
                raise LocalInferenceError("dispatch_not_reversible")
            state["reserved"]["dispatches"] -= item["units"]
            state["reserved"]["requested_output_tokens"] -= item["requested_output_tokens"]
            state["reserved"]["observed_request_wall_ms"] -= item["wall_reserved_ms"]
            item["wall_reserved_ms"] = 0
            item["state"] = "released"
            return _view(item)

        return self._mutate(apply)

    def mark_dispatched(self, dispatch_id: str, *, owner: str) -> dict[str, Any]:
        def apply(state: dict[str, Any]) -> dict[str, Any]:
            item = _owned(state, dispatch_id, owner)
            if item["state"] in {"dispatched", "unknown"}:
                return _view(item)
            if item["state"] != "reserved":
                raise LocalInferenceError("dispatch_not_reversible")
            if item["profile_hash"] != state["segments"][-1]["profile_hash"]:
                raise LocalInferenceError("profile_hash_mismatch")
            state["reserved"]["dispatches"] -= item["units"]
            state["reserved"]["requested_output_tokens"] -= item["requested_output_tokens"]
            state["consumed"]["dispatches"] += item["units"]
            state["consumed"]["requested_output_tokens"] += item["requested_output_tokens"]
            item["state"] = "dispatched"
            return _view(item)

        return self._mutate(apply)

    def mark_unknown(self, dispatch_id: str, *, owner: str) -> dict[str, Any]:
        def apply(state: dict[str, Any]) -> dict[str, Any]:
            item = _owned(state, dispatch_id, owner)
            if item["state"] == "unknown":
                return _view(item)
            if item["state"] != "dispatched":
                raise LocalInferenceError("reservation_not_dispatched")
            item["state"] = "unknown"
            return _view(item)

        return self._mutate(apply)

    def observe_wall(
        self,
        dispatch_id: str,
        *,
        owner: str,
        milliseconds: int,
        receipt: str,
    ) -> dict[str, Any]:
        """Accrue a cumulative request-clock watermark without releasing capacity.

        A receipt identifies one observation clock, not one update. Repeated
        identical watermarks are idempotent. Regressing clocks are rejected.
        Actual elapsed time beyond the grant is recorded as debt, never erased.
        """

        millis = _count(milliseconds, minimum=0, maximum=_MAX_WALL_MS)
        _token(receipt)

        def apply(state: dict[str, Any]) -> dict[str, Any]:
            item = _owned(state, dispatch_id, owner)
            if item["state"] not in {"dispatched", "unknown", "completed"}:
                raise LocalInferenceError("wall_not_observable")
            _accrue_wall(state, item, millis, receipt)
            return _view(item)

        return self._mutate(apply)

    def settle_observed_wall(
        self,
        dispatch_id: str,
        *,
        owner: str,
        milliseconds: int,
        receipt: str,
        completion_known: bool,
    ) -> dict[str, Any]:
        """Close local observation, retaining unused allocation if work is unknown.

        A later verified completion can resolve the same final watermark. It
        cannot change the already-final elapsed measurement or refund a known
        dispatch/output envelope. Merely stopping the HTTP client is not proof
        that remote work completed.
        """

        millis = _count(milliseconds, minimum=0, maximum=_MAX_WALL_MS)
        _token(receipt)
        if type(completion_known) is not bool:
            raise LocalInferenceError("invalid_completion_evidence")

        def apply(state: dict[str, Any]) -> dict[str, Any]:
            item = _owned(state, dispatch_id, owner)
            if item["state"] not in {"dispatched", "unknown", "completed"}:
                raise LocalInferenceError("wall_not_observable")
            if item["state"] == "completed" and not completion_known:
                raise LocalInferenceError("completion_conflict")
            _accrue_wall(state, item, millis, receipt)
            item["wall_final"] = True
            if completion_known:
                state["reserved"]["observed_request_wall_ms"] -= item["wall_reserved_ms"]
                item["wall_reserved_ms"] = 0
                item["state"] = "completed"
            else:
                item["state"] = "unknown"
            return _view(item)

        return self._mutate(apply)

    def record_unresolved(self, dispatch_id: str, *, owner: str, operator_id: str) -> dict[str, Any]:
        """Record uncertainty. This does not refund a dispatch or invent zero usage."""

        _owner(operator_id)

        def apply(state: dict[str, Any]) -> dict[str, Any]:
            item = _owned(state, dispatch_id, owner)
            if item["state"] != "unknown":
                raise LocalInferenceError("reservation_not_unknown")
            if item["unresolved_operator"] not in {None, operator_id}:
                raise LocalInferenceError("dispatch_conflict")
            item["unresolved_operator"] = operator_id
            return _view(item)

        return self._mutate(apply)

    def grant_extension(
        self,
        *,
        operator_id: str,
        dispatches: int = 0,
        requested_output_tokens: int = 0,
        observed_request_wall_s: int = 0,
        reason: str,
    ) -> dict[str, Any]:
        if reason != "operator_grant":
            raise LocalInferenceError("extension_reason_forbidden")
        _owner(operator_id)
        extra_d = _count(dispatches, minimum=0)
        extra_o = _count(requested_output_tokens, minimum=0)
        extra_s = _count(observed_request_wall_s, minimum=0, maximum=1_000_000_000)
        if extra_d == extra_o == extra_s == 0:
            raise LocalInferenceError("empty_extension")

        def apply(state: dict[str, Any]) -> dict[str, Any]:
            if (
                state["ceilings"]["dispatches"] + extra_d > _MAX_COUNT
                or state["ceilings"]["requested_output_tokens"] + extra_o > _MAX_COUNT
                or state["ceilings"]["observed_request_wall_ms"] + extra_s * 1000 > _MAX_WALL_MS
            ):
                raise LocalInferenceError("extension_too_large")
            state["ceilings"]["dispatches"] += extra_d
            state["ceilings"]["requested_output_tokens"] += extra_o
            state["ceilings"]["observed_request_wall_ms"] += extra_s * 1000
            state["extensions"].append({
                "index": len(state["extensions"]) + 1,
                "operator_id": operator_id,
                "reason": "operator_grant",
                "dispatches": extra_d,
                "requested_output_tokens": extra_o,
                "observed_request_wall_ms": extra_s * 1000,
            })
            return {"index": len(state["extensions"]), "reason": "operator_grant"}

        return self._mutate(apply)

    def reconfigure_profile(self, profile_hash: str) -> dict[str, Any]:
        """Point later admissions at a new profile without clearing consumption."""

        _hex(profile_hash, 64)

        def apply(state: dict[str, Any]) -> dict[str, Any]:
            if state["segments"][-1]["profile_hash"] == profile_hash:
                return {"profile_hash": profile_hash, "changed": False}
            state["segments"].append({
                "index": len(state["segments"]),
                "profile_hash": profile_hash,
                "reason": "reconfigure",
            })
            return {"profile_hash": profile_hash, "changed": True}

        return self._mutate(apply)

    def require_resume_identity(self, *, ledger_id: str, profile_hash: str) -> None:
        _hex(ledger_id, 32)
        _hex(profile_hash, 64)
        state = self.snapshot()
        if state["ledger_id"] != ledger_id:
            raise LocalInferenceError("ledger_identity_mismatch")
        if state["segments"][-1]["profile_hash"] != profile_hash:
            raise LocalInferenceError("profile_hash_mismatch")

    def _mutate(self, apply: Any) -> Any:
        with durable_mutation(self.directory):
            state = self._load()
            working = copy_state(state)
            result = apply(working)
            working["mutation_sequence"] = state["mutation_sequence"]
            if working != state:
                working["mutation_sequence"] = state["mutation_sequence"] + 1
                _validate(working)
                atomic_write_json(self.path, working, max_bytes=_MAX_BYTES)
            return result

    def _load(self) -> dict[str, Any]:
        if self.path.is_symlink() or not self.path.is_file():
            raise LocalInferenceError("budget_unavailable")
        state = read_json_object(self.path, max_bytes=_MAX_BYTES, corrupt_code="corrupt_ledger")
        _validate(state)
        return state


class LocalComputeClient:
    """Owner-scoped handle. Extensions and profile changes stay on the parent ledger."""

    def __init__(self, ledger: LocalComputeLedger, owner: str) -> None:
        self.ledger = ledger
        self.owner = owner

    def reserve(
        self, *, dispatch_id: str, requested_output_tokens: int, requested_wall_ms: int,
        units: int = 1, expected_profile_hash: str | None = None,
    ) -> dict[str, Any]:
        return self.ledger.reserve(
            dispatch_id=dispatch_id,
            requested_output_tokens=requested_output_tokens,
            requested_wall_ms=requested_wall_ms,
            units=units,
            owner=self.owner,
            expected_profile_hash=expected_profile_hash,
        )

    def release_not_dispatched(self, dispatch_id: str) -> dict[str, Any]:
        return self.ledger.release_not_dispatched(dispatch_id, owner=self.owner)

    def mark_dispatched(self, dispatch_id: str) -> dict[str, Any]:
        return self.ledger.mark_dispatched(dispatch_id, owner=self.owner)

    def mark_unknown(self, dispatch_id: str) -> dict[str, Any]:
        return self.ledger.mark_unknown(dispatch_id, owner=self.owner)

    def observe_wall(self, dispatch_id: str, *, milliseconds: int, receipt: str) -> dict[str, Any]:
        return self.ledger.observe_wall(
            dispatch_id, owner=self.owner, milliseconds=milliseconds, receipt=receipt,
        )

    def settle_observed_wall(
        self, dispatch_id: str, *, milliseconds: int, receipt: str, completion_known: bool,
    ) -> dict[str, Any]:
        return self.ledger.settle_observed_wall(
            dispatch_id, owner=self.owner, milliseconds=milliseconds, receipt=receipt,
            completion_known=completion_known,
        )


def _wall_remaining(state: dict[str, Any]) -> int:
    return (
        state["ceilings"]["observed_request_wall_ms"]
        - state["consumed"]["observed_request_wall_ms"]
        - state["reserved"]["observed_request_wall_ms"]
    )


def _accrue_wall(state: dict[str, Any], item: dict[str, Any], millis: int, receipt: str) -> None:
    if item["wall_receipt"] is not None and item["wall_receipt"] != receipt:
        raise LocalInferenceError("wall_receipt_conflict")
    if millis < item["wall_ms"] or (item["wall_final"] and millis != item["wall_ms"]):
        raise LocalInferenceError("wall_receipt_conflict")
    delta = millis - item["wall_ms"]
    covered = min(delta, item["wall_reserved_ms"])
    state["reserved"]["observed_request_wall_ms"] -= covered
    item["wall_reserved_ms"] -= covered
    state["consumed"]["observed_request_wall_ms"] += delta
    item["wall_ms"] = millis
    item["wall_receipt"] = receipt


def _require_room(state: dict[str, Any], *, dispatches: int, output_tokens: int) -> None:
    dispatch_left = state["ceilings"]["dispatches"] - state["consumed"]["dispatches"] - state["reserved"]["dispatches"]
    output_left = (
        state["ceilings"]["requested_output_tokens"]
        - state["consumed"]["requested_output_tokens"]
        - state["reserved"]["requested_output_tokens"]
    )
    wall_left = _wall_remaining(state)
    if dispatch_left < dispatches:
        raise LocalInferenceError("allocation_exhausted", "dispatches")
    if output_left < output_tokens:
        raise LocalInferenceError("allocation_exhausted", "output_tokens")
    if wall_left <= 0:
        raise LocalInferenceError("allocation_exhausted", "wall")


def _owned(state: dict[str, Any], dispatch_id: str, owner: str) -> dict[str, Any]:
    _token(dispatch_id)
    _owner(owner)
    item = state["reservations"].get(dispatch_id)
    if item is None:
        raise LocalInferenceError("unknown_reservation")
    if item["owner"] != owner:
        raise LocalInferenceError("owner_mismatch")
    return item


def _view(item: dict[str, Any]) -> dict[str, Any]:
    measured = item["wall_receipt"] is not None
    return {
        "dispatch_id": item["dispatch_id"],
        "owner": item["owner"],
        "state": item["state"],
        "units": item["units"],
        "requested_output_tokens": item["requested_output_tokens"],
        "wall_settled": item["wall_final"],
        "observed_request_wall_ms": item["wall_ms"] if measured else None,
        "granted_wall_ms": item["granted_wall_ms"],
        "reserved_wall_ms": item["wall_reserved_ms"],
        "completion_known": item["state"] == "completed",
        "token_usage_known": False,
    }


def _validate(state: dict[str, Any]) -> None:
    try:
        _validate_inner(state)
    except (LocalInferenceError, KeyError, TypeError, ValueError, OverflowError) as exc:
        if isinstance(exc, LocalInferenceError) and exc.code == "corrupt_ledger":
            raise
        raise LocalInferenceError("corrupt_ledger") from None


def _validate_inner(state: dict[str, Any]) -> None:
    keys = {
        "schema_version", "ledger_id", "mutation_sequence", "segments", "ceilings",
        "consumed", "reserved", "extensions", "reservations",
    }
    if set(state) != keys or type(state["schema_version"]) is not int or state["schema_version"] != 2:
        raise LocalInferenceError("corrupt_ledger")
    _hex(state["ledger_id"], 32)
    if type(state["mutation_sequence"]) is not int or isinstance(state["mutation_sequence"], bool) or state["mutation_sequence"] < 0:
        raise LocalInferenceError("corrupt_ledger")
    ceilings = state["ceilings"]
    consumed = state["consumed"]
    reserved = state["reserved"]
    for name in ("dispatches", "requested_output_tokens", "observed_request_wall_ms"):
        if name == "observed_request_wall_ms":
            continue
        _count(ceilings[name], minimum=1)
        _count(consumed[name], minimum=0)
        _count(reserved[name], minimum=0)
    _count(ceilings["observed_request_wall_ms"], minimum=1, maximum=_MAX_WALL_MS)
    _count(consumed["observed_request_wall_ms"], minimum=0, maximum=_MAX_WALL_MS * _MAX_COUNT)
    _count(reserved["observed_request_wall_ms"], minimum=0, maximum=_MAX_WALL_MS)
    if type(state["segments"]) is not list or not state["segments"] or type(state["extensions"]) is not list:
        raise LocalInferenceError("corrupt_ledger")
    if type(state["reservations"]) is not dict:
        raise LocalInferenceError("corrupt_ledger")
    reserved_d = reserved_o = consumed_d = consumed_o = wall = reserved_wall = 0
    for key, item in state["reservations"].items():
        if type(item) is not dict or key != item.get("dispatch_id"):
            raise LocalInferenceError("corrupt_ledger")
        _token(key)
        _owner(item["owner"])
        _hex(item["profile_hash"], 64)
        _count(item["units"], minimum=1, maximum=10_000)
        _count(item["requested_output_tokens_per_unit"], minimum=1)
        if item["requested_output_tokens"] != item["units"] * item["requested_output_tokens_per_unit"]:
            raise LocalInferenceError("corrupt_ledger")
        _count(item["requested_wall_ms_per_unit"], minimum=1, maximum=_MAX_WALL_MS)
        _count(item["granted_wall_ms"], minimum=1, maximum=item["requested_wall_ms_per_unit"])
        if item["wall_envelope_ms"] != item["granted_wall_ms"] * item["units"]:
            raise LocalInferenceError("corrupt_ledger")
        _count(item["wall_ms"], minimum=0, maximum=_MAX_WALL_MS)
        _count(item["wall_reserved_ms"], minimum=0, maximum=item["wall_envelope_ms"])
        if type(item["wall_final"]) is not bool:
            raise LocalInferenceError("corrupt_ledger")
        if item["state"] == "reserved":
            reserved_d += item["units"]
            reserved_o += item["requested_output_tokens"]
        elif item["state"] in {"dispatched", "unknown", "completed"}:
            consumed_d += item["units"]
            consumed_o += item["requested_output_tokens"]
        elif item["state"] != "released":
            raise LocalInferenceError("corrupt_ledger")
        if item["wall_receipt"] is None:
            if item["wall_ms"] != 0:
                raise LocalInferenceError("corrupt_ledger")
        else:
            _token(item["wall_receipt"])
            wall += item["wall_ms"]
        if item["state"] in {"reserved", "released"} and (item["wall_receipt"] is not None or item["wall_final"]):
            raise LocalInferenceError("corrupt_ledger")
        if item["state"] == "completed" and not item["wall_final"]:
            raise LocalInferenceError("corrupt_ledger")
        expected_reserved = (
            0 if item["state"] in {"released", "completed"}
            else max(0, item["wall_envelope_ms"] - item["wall_ms"])
        )
        if item["wall_reserved_ms"] != expected_reserved:
            raise LocalInferenceError("corrupt_ledger")
        reserved_wall += item["wall_reserved_ms"]
    if reserved_wall != reserved["observed_request_wall_ms"]:
        raise LocalInferenceError("corrupt_ledger")
    if (reserved_d, reserved_o) != (reserved["dispatches"], reserved["requested_output_tokens"]):
        raise LocalInferenceError("corrupt_ledger")
    if (consumed_d, consumed_o, wall) != (
        consumed["dispatches"], consumed["requested_output_tokens"], consumed["observed_request_wall_ms"],
    ):
        raise LocalInferenceError("corrupt_ledger")
    if reserved_d + consumed_d > ceilings["dispatches"] or reserved_o + consumed_o > ceilings["requested_output_tokens"]:
        raise LocalInferenceError("corrupt_ledger")
    previous = ""
    for index, segment in enumerate(state["segments"]):
        if (
            set(segment) != {"index", "profile_hash", "reason"}
            or segment["index"] != index
            or segment["reason"] not in {"create", "reconfigure"}
            or (index == 0 and segment["reason"] != "create")
        ):
            raise LocalInferenceError("corrupt_ledger")
        _hex(segment["profile_hash"], 64)
        if segment["profile_hash"] == previous:
            raise LocalInferenceError("corrupt_ledger")
        previous = segment["profile_hash"]


def _directory(value: str | Path) -> Path:
    path = Path(value)
    if path.is_symlink():
        raise LocalInferenceError("symlink_forbidden")
    return path


def _hex(value: Any, size: int) -> str:
    if type(value) is not str or len(value) != size or any(ch not in "0123456789abcdef" for ch in value):
        raise LocalInferenceError("invalid_field", "profile_hash" if size == 64 else "ledger_id")
    return value


def _count(value: Any, *, minimum: int, maximum: int = _MAX_COUNT) -> int:
    if type(value) is not int or isinstance(value, bool) or value < minimum or value > maximum:
        raise LocalInferenceError("invalid_field", "run_budget")
    return value


def _token(value: str) -> str:
    if type(value) is not str or _RECORD_ID.fullmatch(value) is None:
        raise LocalInferenceError("invalid_dispatch_id")
    return value


def _owner(value: str) -> str:
    if type(value) is not str or _OWNER.fullmatch(value) is None:
        raise LocalInferenceError("invalid_owner")
    return value
