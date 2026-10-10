"""Immutable parked provider receipts with independently readable authority."""

from __future__ import annotations

import copy
import hashlib
from abc import ABC, abstractmethod
from typing import Any, Callable, Mapping

from ensemble_prover.snapshot_codec import compress_snapshot, decompress_snapshot, snapshot_bytes

from .state_codec import StateSnapshotCompatibilityError


_ENVELOPE_KEYS = {"encoding", "sha256", "expanded_bytes", "header", "data"}
_BODY_KEYS = {"checkpoint", "prompt_scope", "context_identity"}
_SCOPE_KEYS = {
    "graph_last_scope_key", "graph_scope_anchor_index", "last_premise_block",
    "last_premise_names", "last_premise_block_injected", "conv_last_llm_content",
}


def validate_provider_prompt_scope(scope: Any, history: list[Any]) -> None:
    if (type(scope) is not dict or set(scope) != _SCOPE_KEYS
            or type(scope["graph_scope_anchor_index"]) is not int
            or not -1 <= scope["graph_scope_anchor_index"] < len(history)
            or any(type(scope[key]) is not str for key in (
                "graph_last_scope_key", "last_premise_block", "conv_last_llm_content"))
            or type(scope["last_premise_block_injected"]) is not bool
            or type(scope["last_premise_names"]) is not list
            or any(type(name) is not str for name in scope["last_premise_names"])):
        raise StateSnapshotCompatibilityError("invalid provider prompt scope")


def _header(body: Mapping[str, Any]) -> dict[str, Any]:
    checkpoint = body["checkpoint"]
    return {
        "lane_id": checkpoint["state"]["provider_turn_lane_identity"],
        "binding": copy.deepcopy(checkpoint["binding"]),
        "context_identity": body["context_identity"],
        "has_pending_tool_replay": bool(checkpoint["state"].get("pending_tool_replay")),
    }


def authenticated_provider_lane_header(body: Mapping[str, Any]) -> dict[str, Any]:
    """Derive routing metadata from an already authenticated decoded body."""
    return _header(body)


def encode_provider_lane(
    checkpoint: dict[str, Any], prompt_scope: dict[str, Any], context_identity: str,
) -> dict[str, Any]:
    """Encode a validated owned value once, when it leaves the active slot."""
    body = {"checkpoint": checkpoint, "prompt_scope": prompt_scope,
            "context_identity": context_identity}
    raw = snapshot_bytes(body)
    return {"encoding": "json-zlib-v1", "sha256": hashlib.sha256(raw).hexdigest(),
            "expanded_bytes": len(raw), "header": _header(body),
            "data": compress_snapshot(body)}


def decode_provider_lane(
    lane_id: str, envelope: Any,
    validate_checkpoint: Callable[[Any], dict[str, Any]],
) -> dict[str, Any]:
    """Authenticate inert input at restore or the selected activation boundary."""
    try:
        if (type(envelope) is not dict or set(envelope) != _ENVELOPE_KEYS
                or envelope["encoding"] != "json-zlib-v1"
                or type(envelope["expanded_bytes"]) is not int
                or envelope["expanded_bytes"] < 0
                or type(envelope["data"]) is not str):
            raise ValueError("invalid envelope")
        body = decompress_snapshot(envelope["data"], max_bytes=envelope["expanded_bytes"])
        raw = snapshot_bytes(body)
        if (type(body) is not dict or set(body) != _BODY_KEYS
                or len(raw) != envelope["expanded_bytes"]
                or hashlib.sha256(raw).hexdigest() != envelope["sha256"]
                or type(body["context_identity"]) is not str
                or len(body["context_identity"]) != 64):
            raise ValueError("invalid body identity")
        checkpoint = validate_checkpoint(body["checkpoint"])
        if not checkpoint or checkpoint != body["checkpoint"]:
            raise ValueError("noncanonical checkpoint")
        expected_header = _header(body)
        header = envelope["header"]
        if type(header) is not dict:
            raise ValueError("invalid header")
        if set(header) == {"lane_id", "binding", "context_identity"}:
            expected_header.pop("has_pending_tool_replay")
        elif type(header.get("has_pending_tool_replay")) is not bool:
            raise ValueError("invalid pending tool routing flag")
        if expected_header != header or header["lane_id"] != lane_id:
            raise ValueError("header ownership mismatch")
        validate_provider_prompt_scope(body["prompt_scope"], checkpoint["history"])
        return body
    except (KeyError, TypeError, ValueError, OverflowError, RecursionError) as error:
        raise StateSnapshotCompatibilityError("parked provider lane is malformed") from error


def copy_provider_envelope(envelope: Mapping[str, Any]) -> dict[str, Any]:
    """Detach mutable authority fields without copying immutable payload bytes."""
    return {**envelope, "header": copy.deepcopy(envelope["header"])}


def provider_context_identity(session: Any) -> str:
    """Bind shared root, Lean inputs and visibility, independently of active B."""
    conv = session.conv
    payload = {key: getattr(conv, key, None) for key in (
        "goal_statement", "lean_signature", "preamble", "lean_preamble", "opaque_mode",
        "allow_official_answer_visibility", "official_answer_payload_present",
        "suppress_solution_placeholders", "allow_helper_decomposition",
    )}
    payload["root_statement"] = getattr(session.dossier, "root_statement", "")
    payload["environment"] = getattr(session.dossier, "current_lean_environment_hash", "")
    return hashlib.sha256(snapshot_bytes(payload)).hexdigest()


def capture_provider_prompt_scope(session: Any, history: list[Any]) -> dict[str, Any]:
    conv = session.conv
    anchor = getattr(conv, "_graph_selected_work_scope_anchor_message", None)
    index = next((i for i, item in enumerate(history) if item == anchor), -1)
    return {
        "graph_last_scope_key": str(getattr(conv, "_graph_selected_work_last_scope_key", "") or ""),
        "graph_scope_anchor_index": index,
        "last_premise_block": str(getattr(session, "last_premise_block", "") or ""),
        "last_premise_names": list(getattr(session, "last_premise_names", ()) or ()),
        "last_premise_block_injected": bool(getattr(session, "_last_premise_block_injected", False)),
        "conv_last_llm_content": str(getattr(conv, "_last_llm_content", "") or ""),
    }


def restore_provider_prompt_scope(session: Any, scope: Mapping[str, Any]) -> None:
    conv = session.conv
    conv._graph_selected_work_last_scope_key = scope["graph_last_scope_key"]
    index = scope["graph_scope_anchor_index"]
    conv._graph_selected_work_scope_anchor_message = conv.history[index] if index >= 0 else None
    conv._graph_selected_work_scope_changed = False
    session.last_premise_block = scope["last_premise_block"]
    session.last_premise_names = list(scope["last_premise_names"])
    session._last_premise_block_injected = scope["last_premise_block_injected"]
    conv._last_llm_content = scope["conv_last_llm_content"]


class ProviderLaneBankMixin(ABC):
    """Action-owned parking; cold payloads are decoded only when selected."""

    id: str
    _provider_quantum_checkpoint: dict[str, Any]
    _provider_quantum_parked: dict[str, dict[str, Any]]
    _provider_quantum_active_context_identity: str
    _provider_quantum_active_prompt_scope: dict[str, Any]
    _provider_quantum_bank_return_scope: dict[str, Any]
    _provider_quantum_active_digest: str
    _provider_quantum_yield_generation: int
    _provider_quantum_yield_consumed_generation: int
    _answer_safe_recheck_pending: dict[str, Any]
    _answer_safe_recheck_parked: dict[str, dict[str, Any]]
    _answer_safe_recheck_held_terminal_provider_failure: dict[str, Any]

    @abstractmethod
    def _validated_provider_quantum_checkpoint(
        self, raw: Any, *, conv: Any = None,
        expected_target: str | None = None, expected_repair_cycle: str | None = None,
    ) -> dict[str, Any]:
        """Validate the host action's provider protocol and binding schema."""
        raise NotImplementedError

    @classmethod
    @abstractmethod
    def _rehydrate_provider_quantum_selected_work_record(
        cls, record: Any, *, target: str,
    ) -> dict[str, Any]:
        """Restore the host action's exact compact target coordinates."""
        raise NotImplementedError

    @staticmethod
    def _provider_lane_has_binding(checkpoint: Mapping[str, Any]) -> bool:
        binding = checkpoint.get("binding")
        state = checkpoint.get("state")
        return bool(
            isinstance(binding, Mapping)
            and {"selected_work_record", "target", "repair_cycle"} <= binding.keys()
            and isinstance(state, Mapping) and state.get("provider_turn_lane_identity")
        )

    def _provider_lane_header(self, checkpoint: Mapping[str, Any], session: Any) -> dict[str, Any]:
        return {
            "lane_id": checkpoint["state"]["provider_turn_lane_identity"],
            "binding": checkpoint["binding"],
            "context_identity": (self._provider_quantum_active_context_identity
                                 or provider_context_identity(session)),
            "has_pending_tool_replay": bool(checkpoint["state"].get("pending_tool_replay")),
        }

    @staticmethod
    def _provider_bank_authority(session: Any) -> tuple[str, str]:
        from .actions.conversation_turn import _provider_formal_evidence_hash

        return provider_context_identity(session), _provider_formal_evidence_hash(session)

    def _provider_lane_status(
        self, session: Any, header: Mapping[str, Any], *, authority: tuple[str, str] | None = None,
    ) -> str:
        from .actions.conversation_turn import _provider_repair_cycle_identity

        context_identity, evidence_hash = authority or self._provider_bank_authority(session)
        if (header["lane_id"] in getattr(session, "provider_turn_retired_lane_identities", ())
                or header["context_identity"] != context_identity):
            return "stale"
        binding = header["binding"]
        record = self._rehydrate_provider_quantum_selected_work_record(
            binding["selected_work_record"], target=binding["target"],
        )
        if _provider_repair_cycle_identity(
            session, record, formal_evidence_hash=evidence_hash,
        ) != binding["repair_cycle"]:
            return "stale"
        return session.provider_checkpoint_graph_retention_status(record, target=binding["target"])

    def _detach_provider_lane_mirror(self, session: Any, lane_id: str) -> None:
        raw = getattr(session.conv, "_provider_call_quantum_state", None)
        if isinstance(raw, Mapping) and raw.get("provider_turn_lane_identity") == lane_id:
            delattr(session.conv, "_provider_call_quantum_state")

    def _drop_active_provider_lane(self, session: Any) -> None:
        lane_id = self._provider_quantum_checkpoint.get("state", {}).get("provider_turn_lane_identity")
        if lane_id:
            self._detach_provider_lane_mirror(session, lane_id)
        self._clear_active_provider_lane()

    def _clear_active_provider_lane(self) -> None:
        """Release action ownership while leaving any independent live mirror."""
        self._provider_quantum_checkpoint = {}
        self._provider_quantum_active_context_identity = ""
        self._provider_quantum_active_prompt_scope = {}
        self._provider_quantum_bank_return_scope = {}
        self._provider_quantum_active_digest = ""

    def _park_active_provider_lane(self, session: Any, *, authority: tuple[str, str] | None = None) -> None:
        if not self._provider_quantum_checkpoint:
            return
        checkpoint = self._validated_provider_quantum_checkpoint(self._provider_quantum_checkpoint)
        header = self._provider_lane_header(checkpoint, session)
        if self._provider_lane_status(session, header, authority=authority) != "stale":
            scope = (self._provider_quantum_bank_return_scope
                     or self._provider_quantum_active_prompt_scope
                     or capture_provider_prompt_scope(session, checkpoint["history"]))
            self._provider_quantum_parked[header["lane_id"]] = encode_provider_lane(
                checkpoint, scope, header["context_identity"],
            )
        self._drop_active_provider_lane(session)

    def _prune_parked_provider_lanes(self, session: Any, *, authority: tuple[str, str] | None = None) -> None:
        if not self._provider_quantum_parked:
            return
        authority = authority or self._provider_bank_authority(session)
        for lane_id, envelope in tuple(self._provider_quantum_parked.items()):
            if self._provider_lane_status(session, envelope["header"], authority=authority) == "stale":
                self._provider_quantum_parked.pop(lane_id, None)

    def _prepare_provider_lane_parking(self, session: Any) -> bool:
        """Return whether an inactive owned slot must skip live-mirror capture."""
        if not self._provider_quantum_checkpoint and not self._provider_quantum_parked:
            return False
        authority = self._provider_bank_authority(session)
        self._prune_parked_provider_lanes(session, authority=authority)
        if not self._provider_quantum_checkpoint:
            return False
        if not self._provider_lane_has_binding(self._provider_quantum_checkpoint):
            return False
        status = self._provider_lane_status(
            session, self._provider_lane_header(self._provider_quantum_checkpoint, session), authority=authority,
        )
        if status != "current":
            self._park_active_provider_lane(session, authority=authority)
            return True
        return bool(self._provider_quantum_bank_return_scope)

    def _provider_lane_dispatch_available(self, session: Any) -> bool:
        if getattr(session, "selected_work_item_record", None):
            return True
        headers = [item["header"] for item in self._provider_quantum_parked.values()]
        if self._provider_quantum_checkpoint:
            if not self._provider_lane_has_binding(self._provider_quantum_checkpoint):
                return True
            headers.append(self._provider_lane_header(self._provider_quantum_checkpoint, session))
        if not headers:
            return True
        authority = self._provider_bank_authority(session)
        return any(self._provider_lane_status(session, header, authority=authority) == "current" for header in headers)

    @staticmethod
    def _provider_selected_cycle(session: Any, authority: tuple[str, str]) -> str:
        from .actions.conversation_turn import _provider_repair_cycle_identity

        selected = getattr(session, "selected_work_item_record", {}) or {}
        return _provider_repair_cycle_identity(
            session, selected, formal_evidence_hash=authority[1],
        ) if selected else ""

    @staticmethod
    def _provider_lane_matches_selection(header: Mapping[str, Any], selected_cycle: str) -> bool:
        return not selected_cycle or header["binding"]["repair_cycle"] == selected_cycle

    def _has_current_paid_provider_lane(self, session: Any, *, local_replay_only: bool = False) -> bool:
        """Recognize the exact paid lane without expanding any cold payload.

        Existing paid-state policy accepts a nonempty provider lane identity.
        Park/import validation requires that identity and authenticates it in
        the header, so the header is already the complete eligibility receipt.
        """
        headers = [envelope["header"] for envelope in self._provider_quantum_parked.values()]
        if self._provider_quantum_checkpoint:
            try:
                checkpoint = self._validated_provider_quantum_checkpoint(
                    self._provider_quantum_checkpoint, conv=session.conv,
                )
            except StateSnapshotCompatibilityError:
                checkpoint = {}
            if checkpoint:
                headers.append(self._provider_lane_header(checkpoint, session))
        if not headers:
            return False
        authority = self._provider_bank_authority(session)
        selected_cycle = self._provider_selected_cycle(session, authority)
        return any(
            header["lane_id"]
            and (not local_replay_only or header.get("has_pending_tool_replay") is True)
            and self._provider_lane_matches_selection(header, selected_cycle)
            and self._provider_lane_status(session, header, authority=authority) == "current"
            for header in headers
        )

    def _select_provider_lane(self, session: Any, *, local_replay_only: bool = False) -> bool:
        """Honor explicit B, or recover one runnable owned lane without root fallback."""
        had_paid = bool(self._provider_quantum_checkpoint or self._provider_quantum_parked)
        if not had_paid:
            return not local_replay_only
        authority = self._provider_bank_authority(session)
        self._prune_parked_provider_lanes(session, authority=authority)
        selected = getattr(session, "selected_work_item_record", {}) or {}
        selected_cycle = self._provider_selected_cycle(session, authority)
        active = self._provider_quantum_checkpoint
        if active:
            if not self._provider_lane_has_binding(active):
                # Local preflight owns its neutral unavailable-checker return;
                # ordinary activation still validates malformed legacy cursors.
                return not local_replay_only
            header = self._provider_lane_header(active, session)
            status = self._provider_lane_status(session, header, authority=authority)
            if (status != "current" or not self._provider_lane_matches_selection(header, selected_cycle)
                    or (local_replay_only and header.get("has_pending_tool_replay") is not True)):
                self._park_active_provider_lane(session, authority=authority)
            else:
                if self._provider_quantum_bank_return_scope and not selected:
                    binding = active["binding"]
                    record = self._rehydrate_provider_quantum_selected_work_record(
                        binding["selected_work_record"], target=binding["target"],
                    )
                    if record and not session._restore_selected_work_record(record, self.id):
                        return False
                return True
        waiting_selected = False
        for lane_id, envelope in tuple(self._provider_quantum_parked.items()):
            header = envelope["header"]
            if local_replay_only and header.get("has_pending_tool_replay") is not True:
                continue
            if not self._provider_lane_matches_selection(header, selected_cycle):
                continue
            status = self._provider_lane_status(session, header, authority=authority)
            if status != "current":
                waiting_selected = True
                continue
            body = decode_provider_lane(lane_id, envelope, self._validated_provider_quantum_checkpoint)
            binding = body["checkpoint"]["binding"]
            if not selected:
                record = self._rehydrate_provider_quantum_selected_work_record(
                    binding["selected_work_record"], target=binding["target"],
                )
                if record and not session._restore_selected_work_record(record, self.id):
                    continue
            self._provider_quantum_checkpoint = body["checkpoint"]
            self._provider_quantum_active_context_identity = body["context_identity"]
            self._provider_quantum_bank_return_scope = body["prompt_scope"]
            self._refresh_active_provider_digest()
            self._provider_quantum_parked.pop(lane_id)
            return True
        if local_replay_only or waiting_selected or (not selected and had_paid):
            return False
        return True

    def provider_lane_runtime_identity(self) -> dict[str, Any]:
        """Dispatch identity uses authenticated immutable body hashes, not bodies."""
        return {
            "active": self._provider_quantum_active_digest if self._provider_quantum_checkpoint else "",
            "parked": {lane_id: envelope["sha256"]
                       for lane_id, envelope in self._provider_quantum_parked.items()},
            "verifier_pending": self._answer_safe_recheck_pending,
            "verifier_parked": self._answer_safe_recheck_parked,
            "verifier_parked_order": list(self._answer_safe_recheck_parked),
            "held_terminal": self._answer_safe_recheck_held_terminal_provider_failure,
            "yield_generation": self._provider_quantum_yield_generation,
            "yield_consumed_generation": self._provider_quantum_yield_consumed_generation,
            "active_context": self._provider_quantum_active_context_identity if self._provider_quantum_checkpoint else "",
            "active_prompt_scope": (
                self._provider_quantum_bank_return_scope or self._provider_quantum_active_prompt_scope
            ) if self._provider_quantum_checkpoint else {},
            "activation_pending": bool(self._provider_quantum_bank_return_scope),
        }

    def _refresh_active_provider_digest(self) -> None:
        self._provider_quantum_active_digest = (
            hashlib.sha256(snapshot_bytes(self._provider_quantum_checkpoint)).hexdigest()
            if self._provider_quantum_checkpoint else ""
        )
