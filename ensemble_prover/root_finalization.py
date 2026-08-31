"""Canonical gate for committing a verified active-root solution.

``finalize_root_solution`` validates the candidate's target, dependencies,
requested route contract, and deadline transaction before it synchronizes
solved state across the dossier and proof graph. It validates a verification
certificate only when the caller sets ``require_verification_certificate``.
"""

from __future__ import annotations

import copy
import re
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, Iterable, Optional, Tuple

from .lean_artifact_sanitize import (
    sanitize_lean_artifact_text,
    sanitize_lean_artifact_texts,
)
from .mini_deadline_transaction import DeadlineMutationTransaction
from .proof_dossier import (
    _record_falsification_trust_boundary_conflict,
    active_root_disproof_certificate_is_valid,
    helper_decl_name,
    text_hash,
)
from .proof_state import lean_referenced_helper_names


@dataclass(frozen=True)
class RootFinalizationCandidate:
    """Typed candidate for closing the active root theorem."""

    proof: str
    replay_helpers: Tuple[str, ...] = ()
    helper_names: Tuple[str, ...] = ()
    phase: str = ""
    turn_index: int = 0
    source_action_id: str = ""
    route_id: str = ""
    dependency_node_ids: Tuple[str, ...] = ()
    dependency_helper_names: Tuple[str, ...] = ()
    target_statement: str = ""
    require_route_contract: bool = False
    verification_certificate: Dict[str, Any] = field(default_factory=dict)
    metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class RootFinalizationResult:
    """Outcome of applying the canonical root-solve gate."""

    accepted: bool
    proof: str = ""
    verdict: str = ""
    helper_names: Tuple[str, ...] = ()
    route_contract_status: Dict[str, Any] = field(default_factory=dict)
    verification_status: Dict[str, Any] = field(default_factory=dict)
    exception_type: str = ""
    exception_message: str = ""


class _RootProofFinalizationReceiptParticipant:
    """Publish proof recovery authority at the outer deadline commit point."""

    def __init__(self, dossier: Any) -> None:
        self._dossier = dossier
        self._receipt_hash = str(
            dossier.root_proof_finalization_receipt_hash() or ""
        ).strip()
        self._promoted = False

    def commit(self) -> bool:
        return bool(self._receipt_hash)

    def finalize(self) -> bool:
        if (
            not self._receipt_hash
            or self._dossier.root_proof_finalization_receipt_hash()
            != self._receipt_hash
        ):
            return False
        self._dossier._root_proof_finalization_receipts.add(
            self._receipt_hash
        )
        self._promoted = True
        return True

    def rollback(self) -> None:
        if self._promoted:
            self._dossier._root_proof_finalization_receipts.discard(
                self._receipt_hash
            )
        self._promoted = False


def root_verification_certificate(
    *,
    proof: str,
    verifier: str = "lean",
    accepted: bool = False,
    phase: str = "",
    turn_index: int = 0,
    target_statement: str = "",
    replay_helpers: Iterable[str] = (),
    helper_names: Iterable[str] = (),
    output: str = "",
    source: str = "",
    metadata: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    """Build a compact certificate for a root proof accepted by a verifier."""

    proof_text = str(proof or "")
    helper_blocks = tuple(
        str(block or "").strip()
        for block in list(replay_helpers or ())
        if str(block or "").strip()
    )
    helper_name_tuple = tuple(
        str(name or "").strip()
        for name in list(helper_names or ())
        if str(name or "").strip()
    )
    return {
        "verifier": str(verifier or "lean"),
        "accepted": bool(accepted),
        "proof_hash": text_hash(proof_text),
        "target_statement_hash": text_hash(target_statement),
        "helper_source_hashes": [text_hash(block) for block in helper_blocks],
        "helper_names": list(helper_name_tuple),
        "phase": str(phase or ""),
        "turn_index": int(turn_index or 0),
        "source": str(source or ""),
        "output_hash": text_hash(output),
        **dict(metadata or {}),
    }


def _verification_certificate_status(
    *,
    certificate: Optional[Dict[str, Any]],
    proof: str,
    target_statement: str,
    replay_helpers: Tuple[str, ...],
    helper_names: Tuple[str, ...] = (),
    require_certificate: bool,
) -> Dict[str, Any]:
    if not require_certificate:
        return {
            "ready": True,
            "verdict": "root_finalization_certificate_not_required",
        }
    if not isinstance(certificate, dict) or not certificate:
        return {
            "ready": False,
            "verdict": "root_finalization_missing_verification_certificate",
        }
    accepted = any(
        certificate.get(key) is True
        for key in ("accepted", "lean_accepted", "ok")
        if key in certificate
    )
    if not accepted:
        return {
            "ready": False,
            "verdict": "root_finalization_certificate_not_accepted",
        }
    expected_proof_hash = text_hash(proof)
    proof_hash = str(certificate.get("proof_hash") or "").strip()
    if not proof_hash:
        return {
            "ready": False,
            "verdict": "root_finalization_certificate_missing_proof_hash",
        }
    if proof_hash != expected_proof_hash:
        return {
            "ready": False,
            "verdict": "root_finalization_certificate_proof_mismatch",
            "expected_proof_hash": expected_proof_hash,
            "certificate_proof_hash": proof_hash,
        }
    target_hash = str(certificate.get("target_statement_hash") or "").strip()
    if str(target_statement or "").strip() and not target_hash:
        return {
            "ready": False,
            "verdict": "root_finalization_certificate_missing_target_hash",
        }
    if target_hash and str(target_statement or "").strip():
        expected_target_hash = text_hash(target_statement)
        if target_hash != expected_target_hash:
            return {
                "ready": False,
                "verdict": "root_finalization_certificate_target_mismatch",
                "expected_target_statement_hash": expected_target_hash,
                "certificate_target_statement_hash": target_hash,
            }
    helper_hashes = certificate.get("helper_source_hashes")
    if replay_helpers and "helper_source_hashes" not in certificate:
        return {
            "ready": False,
            "verdict": "root_finalization_certificate_missing_helper_hashes",
        }
    if helper_names and not replay_helpers:
        return {
            "ready": False,
            "verdict": "root_finalization_certificate_missing_helper_replay",
            "helper_names": list(helper_names),
        }
    clean_helper_names = tuple(
        str(name or "").strip()
        for name in list(helper_names or ())
        if str(name or "").strip()
    )
    certificate_helper_names = tuple(
        str(name or "").strip()
        for name in list(certificate.get("helper_names") or ())
        if str(name or "").strip()
    )
    if clean_helper_names and (
        not certificate_helper_names
        or sorted(certificate_helper_names) != sorted(clean_helper_names)
    ):
        return {
            "ready": False,
            "verdict": "root_finalization_certificate_helper_name_mismatch",
            "expected_helper_names": sorted(clean_helper_names),
            "certificate_helper_names": sorted(certificate_helper_names),
        }
    if clean_helper_names and replay_helpers:
        declared_helper_names = tuple(
            str(helper_decl_name(block) or "").strip()
            for block in replay_helpers
            if str(helper_decl_name(block) or "").strip()
        )
        if sorted(declared_helper_names) != sorted(clean_helper_names):
            return {
                "ready": False,
                "verdict": "root_finalization_certificate_helper_name_mismatch",
                "expected_helper_names": sorted(clean_helper_names),
                "replay_declared_helper_names": sorted(declared_helper_names),
            }
    if helper_hashes is not None:
        expected_helper_hashes = [text_hash(block) for block in replay_helpers]
        if sorted(str(item or "") for item in list(helper_hashes or ())) != sorted(
            expected_helper_hashes
        ):
            return {
                "ready": False,
                "verdict": "root_finalization_certificate_helper_mismatch",
                "expected_helper_source_hashes": sorted(expected_helper_hashes),
                "certificate_helper_source_hashes": sorted(
                    str(item or "") for item in list(helper_hashes or ())
                ),
            }
    return {
        "ready": True,
        "verdict": "root_finalization_certificate_ready",
        "proof_hash": expected_proof_hash,
        "verifier": str(certificate.get("verifier") or ""),
    }


def _increment_metric(dossier: Any, key: str, amount: int = 1) -> None:
    increment = getattr(dossier, "increment_tool_metric", None)
    if not callable(increment):
        return
    try:
        increment(key, amount)
    except Exception:
        return


def _helper_names_from_blocks(blocks: Iterable[str]) -> Tuple[str, ...]:
    names: list[str] = []
    for block in blocks or ():
        name = helper_decl_name(str(block or ""))
        if name and name not in names:
            names.append(name)
    return tuple(names)


def _candidate_helper_names(
    helper_names: Iterable[str],
    replay_helpers: Iterable[str],
) -> Tuple[str, ...]:
    names: list[str] = []
    for raw in list(helper_names or ()):
        name = str(raw or "").strip()
        if name and name not in names:
            names.append(name)
    for name in _helper_names_from_blocks(replay_helpers):
        if name not in names:
            names.append(name)
    return tuple(names)


_BROAD_CONTEXT_TACTIC_RE = re.compile(
    r"(?<![\w'.])"
    r"(?:simp(?:a)?|aesop|exact\?|omega|linarith|nlinarith|ring_nf|"
    r"norm_num|positivity|field_simp|tauto|decide)"
    r"(?![\w'])"
)


def _proof_may_use_helper_context_implicitly(proof: str) -> bool:
    """Whether Lean may consult replay helpers without naming them explicitly."""

    return bool(_BROAD_CONTEXT_TACTIC_RE.search(str(proof or "")))


def _candidate_dependency_helper_names(
    *,
    proof: str,
    replay_helper_names: Iterable[str],
    replay_helpers: Iterable[str] = (),
    dependency_helper_names: Iterable[str] = (),
) -> Tuple[str, ...]:
    """Return helper names the proof should be treated as depending on.

    Replay helpers are the Lean environment needed to re-run a certificate.
    Dependency helpers are the graph support actually used by the root proof.
    Named dependencies win; otherwise explicit proof references are enough for
    most tactic stubs. Search/simplification tactics may consult attributed
    environment declarations without spelling names, so only helpers whose
    source carries a tactic-relevant attribute are treated as ambient support.
    """

    replay_names = tuple(
        str(name or "").strip()
        for name in list(replay_helper_names or ())
        if str(name or "").strip()
    )
    names: list[str] = []
    for raw in list(dependency_helper_names or ()):
        name = str(raw or "").strip()
        if name and name not in names:
            names.append(name)
    if not replay_names:
        return tuple(names)
    proof_text = str(proof or "")
    if _proof_may_use_helper_context_implicitly(proof_text):
        for name in _ambient_dependency_helper_names(
            proof=proof_text,
            replay_helpers=replay_helpers,
        ):
            if name not in names:
                names.append(name)
    referenced = lean_referenced_helper_names(proof_text, replay_names)
    for name in referenced:
        if name in replay_names and name not in names:
            names.append(name)
    return tuple(names)


def _helper_decl_attribute_text(block: str) -> str:
    stripped = str(block or "").lstrip()
    attrs: list[str] = []
    while stripped.startswith("@["):
        end = stripped.find("]")
        if end < 0:
            break
        attrs.append(stripped[2:end])
        stripped = stripped[end + 1 :].lstrip()
    return " ".join(attrs)


def _ambient_dependency_helper_names(
    *,
    proof: str,
    replay_helpers: Iterable[str],
) -> Tuple[str, ...]:
    proof_text = str(proof or "")
    names: list[str] = []
    for block in list(replay_helpers or ()):
        source = str(block or "")
        name = helper_decl_name(source)
        if not name or name in names:
            continue
        attrs = _helper_decl_attribute_text(source)
        if not attrs:
            continue
        if re.search(r"(?<![\w'.])simp(?:a)?(?![\w'])", proof_text) and re.search(
            r"(?<![\w'.])simp(?![\w'])",
            attrs,
        ):
            names.append(name)
            continue
        if re.search(r"(?<![\w'.])aesop(?![\w'])", proof_text) and re.search(
            r"(?<![\w'.])aesop(?![\w'])",
            attrs,
        ):
            names.append(name)
    return tuple(names)


def _helper_support_closure(dossier: Any, helper_names: Iterable[str]) -> Tuple[str, ...]:
    helpers = getattr(dossier, "verified_helpers", {}) or {}
    seen: set[str] = set()
    stack = [
        str(name or "").strip()
        for name in list(helper_names or ())
        if str(name or "").strip()
    ]
    while stack:
        name = stack.pop()
        if not name or name in seen:
            continue
        seen.add(name)
        helper = helpers.get(name) if isinstance(helpers, dict) else None
        for support in list(getattr(helper, "support_names", []) or []):
            support_name = str(support or "").strip()
            if support_name and support_name not in seen:
                stack.append(support_name)
    return tuple(sorted(seen))


def _route_candidate_support_status(
    dossier: Any,
    *,
    route_contract_status: Dict[str, Any],
    helper_names: Tuple[str, ...],
) -> Dict[str, Any]:
    """Check that the candidate's declared helper support belongs to the route."""

    graph = getattr(dossier, "proof_graph", None)
    graph_nodes = getattr(graph, "nodes", {}) if graph is not None else {}
    if not isinstance(graph_nodes, dict):
        return {"ready": True, "verdict": "route_support_graph_unavailable"}

    expected: list[str] = []
    for node_id in list(
        route_contract_status.get("required_node_ids")
        or route_contract_status.get("dependency_node_ids")
        or []
    ):
        node = graph_nodes.get(str(node_id or "").strip())
        if node is None:
            continue
        metadata = dict(getattr(node, "metadata", {}) or {})
        for raw_name in (
            getattr(node, "name", "") if getattr(node, "kind", "") == "helper" else "",
            metadata.get("verified_by_helper_name"),
            metadata.get("resolved_by_helper_name"),
        ):
            name = str(raw_name or "").strip()
            if name and name not in expected:
                expected.append(name)
    allowed = set(_helper_support_closure(dossier, expected))
    candidate = {
        str(name or "").strip()
        for name in list(helper_names or ())
        if str(name or "").strip()
    }
    if not expected:
        if candidate:
            return {
                "ready": False,
                "verdict": "route_candidate_helper_support_mismatch",
                "route_helper_names": [],
                "allowed_helper_names": [],
                "candidate_helper_names": sorted(candidate),
                "extra_helper_names": sorted(candidate),
            }
        return {"ready": True, "verdict": "route_support_no_helper_dependencies"}
    if not candidate:
        return {
            "ready": False,
            "verdict": "route_candidate_missing_declared_helper_support",
            "route_helper_names": sorted(expected),
        }
    extra = sorted(name for name in candidate if name not in allowed)
    if extra:
        return {
            "ready": False,
            "verdict": "route_candidate_helper_support_mismatch",
            "route_helper_names": sorted(expected),
            "allowed_helper_names": sorted(allowed),
            "candidate_helper_names": sorted(candidate),
            "extra_helper_names": extra,
        }
    return {
        "ready": True,
        "verdict": "route_candidate_helper_support_matches",
        "route_helper_names": sorted(expected),
        "candidate_helper_names": sorted(candidate),
    }


def _route_contract_status(
    dossier: Any,
    *,
    route_id: str,
    proof: str,
    replay_helpers: Tuple[str, ...],
    phase: str,
    turn_index: int,
    target_statement: str,
    require_route_contract: bool,
) -> Dict[str, Any]:
    graph = getattr(dossier, "proof_graph", None)
    clean_route_id = str(route_id or "").strip()
    if clean_route_id:
        status_getter = getattr(graph, "route_assembly_contract_status", None)
        if not callable(status_getter):
            return {
                "ready": False,
                "verdict": "route_assembly_contract_status_api_missing",
                "route_id": clean_route_id,
            }
        try:
            return dict(
                status_getter(
                    clean_route_id,
                    target_statement=str(
                        target_statement
                        or getattr(dossier, "root_statement", "")
                        or ""
                    ),
                )
                or {}
            )
        except Exception as exc:
            return {
                "ready": False,
                "verdict": "route_assembly_contract_status_exception",
                "route_id": clean_route_id,
                "exception_type": type(exc).__name__,
            }

    if not replay_helpers and not require_route_contract:
        return {
            "ready": True,
            "verdict": "root_finalization_no_helper_dependencies",
            "helper_names": [],
        }

    if require_route_contract and not clean_route_id:
        return {
            "ready": False,
            "verdict": "missing_required_root_route_contract",
        }

    try:
        from .mini_root_tactic import root_tactic_success_contract_status

        status = dict(
            root_tactic_success_contract_status(
                dossier,
                proof=proof,
                helper_blocks=list(replay_helpers or ()),
                phase=phase or "root_finalization",
                turn_index=turn_index,
                target_statement=str(
                    target_statement
                    or getattr(dossier, "root_statement", "")
                    or ""
                ),
            )
            or {}
        )
    except Exception as exc:
        return {
            "ready": False,
            "verdict": "root_finalization_contract_check_exception",
            "exception_type": type(exc).__name__,
        }
    if require_route_contract and str(status.get("verdict") or "") in {
        "root_tactic_no_helper_dependencies",
        "root_finalization_no_helper_dependencies",
    }:
        status = dict(status)
        status["ready"] = False
        status["verdict"] = "missing_required_root_route_contract"
    return status


def _ready_root_assembly_contract_status(
    dossier: Any,
    *,
    target_statement: str = "",
) -> Dict[str, Any]:
    graph = getattr(dossier, "proof_graph", None)
    getter = getattr(graph, "ready_root_assembly_contract_status", None)
    if not callable(getter):
        return {
            "ready": False,
            "verdict": "ready_root_assembly_contract_status_api_missing",
        }
    try:
        return dict(
            getter(
                target_statement=str(
                    target_statement
                    or getattr(dossier, "root_statement", "")
                    or ""
                ),
            )
            or {}
        )
    except Exception as exc:
        return {
            "ready": False,
            "verdict": "ready_root_assembly_contract_status_exception",
            "exception_type": type(exc).__name__,
        }


def _ready_root_assembly_contract_status_for_helper_support(
    dossier: Any,
    *,
    target_statement: str = "",
    helper_names: Iterable[str] = (),
) -> Dict[str, Any]:
    graph = getattr(dossier, "proof_graph", None)
    route_iter = getattr(graph, "nodes_by_kind", None)
    status_getter = getattr(graph, "route_assembly_contract_status", None)
    if not callable(route_iter) or not callable(status_getter):
        return _ready_root_assembly_contract_status(
            dossier,
            target_statement=target_statement,
        )
    checked: list[Dict[str, Any]] = []
    for route in list(route_iter("strategy_route") or ()):
        metadata = dict(getattr(route, "metadata", {}) or {})
        contract = metadata.get("route_assembly_contract")
        route_scope = str(metadata.get("route_scope") or "").strip()
        contract_scope = (
            str(contract.get("scope") or "").strip()
            if isinstance(contract, dict)
            else ""
        )
        if route_scope != "root_assembly" and contract_scope != "root_assembly":
            continue
        route_id = str(getattr(route, "node_id", "") or "").strip()
        if not route_id:
            continue
        try:
            status = dict(
                status_getter(
                    route_id,
                    target_statement=str(
                        target_statement
                        or getattr(dossier, "root_statement", "")
                        or ""
                    ),
                )
                or {}
            )
        except Exception as exc:
            checked.append(
                {
                    "route_id": route_id,
                    "ready": False,
                    "verdict": "route_assembly_contract_status_exception",
                    "exception_type": type(exc).__name__,
                }
            )
            continue
        if not bool(status.get("ready")):
            checked.append(
                {
                    "route_id": route_id,
                    "ready": False,
                    "verdict": str(status.get("verdict") or ""),
                }
            )
            continue
        status.setdefault("route_id", route_id)
        support_status = _route_candidate_support_status(
            dossier,
            route_contract_status=status,
            helper_names=tuple(helper_names or ()),
        )
        if bool(support_status.get("ready")):
            return {
                **status,
                "candidate_support_status": dict(support_status),
            }
        checked.append(
            {
                "route_id": route_id,
                "ready": True,
                "verdict": str(status.get("verdict") or ""),
                "candidate_support_status": dict(support_status),
            }
        )
    return {
        "ready": False,
        "verdict": "missing_support_compatible_ready_root_assembly_contract",
        "checked_route_count": len(checked),
        "checked_route_contracts": checked[:8],
    }


def _root_assembly_route_context_exists(contract_status: Dict[str, Any]) -> bool:
    if bool(contract_status.get("ready")):
        return True
    if str(contract_status.get("route_id") or "").strip():
        return True
    try:
        if int(contract_status.get("checked_route_count") or 0) > 0:
            return True
    except (TypeError, ValueError):
        return True
    verdict = str(contract_status.get("verdict") or "").strip()
    if verdict == "missing_ready_root_assembly_contract":
        return False
    return bool(verdict)


def _store_root_finalization_metadata(
    dossier: Any,
    *,
    route_id: str,
    dependency_node_ids: Iterable[str],
    dependency_helper_names: Iterable[str],
    helper_names: Iterable[str],
    require_route_contract: bool,
    contract_status: Dict[str, Any],
    verification_status: Dict[str, Any],
    verification_certificate: Optional[Dict[str, Any]],
) -> None:
    graph = getattr(dossier, "proof_graph", None) if dossier is not None else None
    if graph is None:
        return
    try:
        root = graph.ensure_root(getattr(graph, "root_statement", ""))
    except Exception:
        root = None
    if root is None:
        return
    metadata = getattr(root, "metadata", None)
    if not isinstance(metadata, dict):
        return
    clean_route_id = str(route_id or "").strip()
    if clean_route_id:
        metadata["root_finalization_route_id"] = clean_route_id
    else:
        metadata.pop("root_finalization_route_id", None)
    metadata["root_finalization_dependency_node_ids"] = [
        str(item or "").strip()
        for item in list(dependency_node_ids or ())
        if str(item or "").strip()
    ]
    metadata["root_finalization_helper_names"] = [
        str(item or "").strip()
        for item in list(helper_names or ())
        if str(item or "").strip()
    ]
    metadata["root_finalization_dependency_helper_names"] = [
        str(item or "").strip()
        for item in list(dependency_helper_names or ())
        if str(item or "").strip()
    ]
    metadata["root_finalization_require_route_contract"] = bool(
        require_route_contract
    )
    if contract_status:
        metadata["root_finalization_contract_status"] = dict(contract_status)
    else:
        metadata.pop("root_finalization_contract_status", None)
    if verification_status:
        metadata["root_finalization_verification_status"] = dict(verification_status)
    else:
        metadata.pop("root_finalization_verification_status", None)
    if isinstance(verification_certificate, dict) and verification_certificate:
        metadata["root_finalization_verification_certificate"] = dict(
            verification_certificate
        )
    else:
        metadata.pop("root_finalization_verification_certificate", None)


def _finalize_root_solution_impl(
    *,
    dossier: Any,
    proof_state: Optional[Any] = None,
    proof: str,
    replay_helpers: Iterable[str] = (),
    helper_names: Iterable[str] = (),
    phase: str = "",
    turn_index: int = 0,
    source_action_id: str = "",
    route_id: str = "",
    dependency_node_ids: Iterable[str] = (),
    dependency_helper_names: Iterable[str] = (),
    target_statement: str = "",
    require_route_contract: bool = False,
    verification_certificate: Optional[Dict[str, Any]] = None,
    require_verification_certificate: bool = False,
    record_attempt: bool = True,
    persist_solution: bool = True,
    metadata: Optional[Dict[str, Any]] = None,
    deadline_exhausted: Optional[Callable[[], bool]] = None,
) -> RootFinalizationResult:
    """Validate and persist a root solution candidate.

    This function is intentionally defensive: if route-contract validation
    blocks, root state is left untouched and a rejected attempt is recorded
    when possible.  If mutation fails partway through, the caller receives a
    non-accepted result instead of a raw exception.
    """

    verification_proof_text = str(proof or "")
    artifact_proof_text = sanitize_lean_artifact_text(verification_proof_text)
    if not artifact_proof_text.strip():
        return RootFinalizationResult(
            accepted=False,
            verdict="root_finalization_empty_proof",
        )
    proof_text = artifact_proof_text

    def deadline_elapsed() -> bool:
        try:
            return bool(deadline_exhausted and deadline_exhausted())
        except Exception:
            return True

    if deadline_elapsed():
        return RootFinalizationResult(
            accepted=False,
            proof=proof_text,
            verdict="llm_turn_elapsed_budget_exhausted",
        )

    verification_replay_helper_tuple = tuple(
        str(block or "").strip()
        for block in list(replay_helpers or ())
        if str(block or "").strip()
    )
    artifact_replay_helper_tuple = sanitize_lean_artifact_texts(
        verification_replay_helper_tuple
    )
    replay_helper_tuple = artifact_replay_helper_tuple
    final_helper_names = _candidate_helper_names(
        helper_names,
        artifact_replay_helper_tuple,
    )
    final_dependency_helper_names = _candidate_dependency_helper_names(
        proof=proof_text,
        replay_helper_names=final_helper_names,
        replay_helpers=replay_helper_tuple,
        dependency_helper_names=dependency_helper_names,
    )
    phase_text = str(phase or source_action_id or "root_finalization")
    clean_route_id = str(route_id or "").strip()
    clean_dependency_node_ids = tuple(
        str(item or "").strip()
        for item in list(dependency_node_ids or ())
        if str(item or "").strip()
    )
    contract_status: Dict[str, Any] = {}
    if dossier is not None and record_attempt:
        _increment_metric(dossier, "mini_root_finalization_candidates", 1)
    supplied_target_statement = str(target_statement or "").strip()
    dossier_root_statement = str(
        getattr(dossier, "root_statement", "") or ""
    ).strip()
    effective_target_statement = dossier_root_statement or supplied_target_statement
    if (
        supplied_target_statement
        and dossier_root_statement
        and text_hash(supplied_target_statement) != text_hash(dossier_root_statement)
    ):
        target_status = {
            "ready": False,
            "verdict": "root_finalization_target_mismatch",
            "expected_target_statement_hash": text_hash(dossier_root_statement),
            "candidate_target_statement_hash": text_hash(supplied_target_statement),
        }
        if dossier is not None and record_attempt:
            _increment_metric(dossier, "mini_root_finalization_blocked", 1)
            _increment_metric(dossier, "mini_root_finalization_target_mismatch", 1)
            recorder = getattr(dossier, "record_attempt", None)
            if callable(recorder):
                try:
                    recorder(
                        phase=phase_text,
                        turn_index=int(turn_index or 0),
                        proof=verification_proof_text,
                        helper_names=final_helper_names,
                        verdict="root_finalization_target_mismatch",
                        metadata={
                            "root_finalization_gate": True,
                            "root_verification_status": dict(target_status),
                            "source_action_id": str(source_action_id or ""),
                            "route_id": clean_route_id,
                            "dependency_node_ids": list(clean_dependency_node_ids),
                            "dependency_helper_names": list(
                                final_dependency_helper_names
                            ),
                            **dict(metadata or {}),
                        },
                    )
                except Exception:
                    pass
        return RootFinalizationResult(
            accepted=False,
            proof=verification_proof_text,
            verdict="root_finalization_target_mismatch",
            helper_names=final_dependency_helper_names,
            route_contract_status=contract_status,
            verification_status=target_status,
        )
    certificate_status = _verification_certificate_status(
        certificate=verification_certificate,
        proof=verification_proof_text,
        target_statement=effective_target_statement,
        replay_helpers=verification_replay_helper_tuple,
        helper_names=final_helper_names,
        require_certificate=bool(require_verification_certificate),
    )
    if not bool(certificate_status.get("ready")):
        if dossier is not None and record_attempt:
            _increment_metric(dossier, "mini_root_finalization_blocked", 1)
            metric = (
                "mini_root_finalization_missing_certificate"
                if str(certificate_status.get("verdict") or "")
                == "root_finalization_missing_verification_certificate"
                else "mini_root_finalization_certificate_rejected"
            )
            _increment_metric(dossier, metric, 1)
            recorder = getattr(dossier, "record_attempt", None)
            if callable(recorder):
                try:
                    recorder(
                        phase=phase_text,
                        turn_index=int(turn_index or 0),
                        proof=verification_proof_text,
                        helper_names=final_helper_names,
                        verdict=str(
                            certificate_status.get("verdict")
                            or "root_finalization_certificate_rejected"
                        ),
                        metadata={
                            "root_finalization_gate": True,
                            "root_verification_status": dict(certificate_status),
                            "source_action_id": str(source_action_id or ""),
                            "route_id": clean_route_id,
                            "dependency_node_ids": list(clean_dependency_node_ids),
                            "dependency_helper_names": list(
                                final_dependency_helper_names
                            ),
                            **dict(metadata or {}),
                        },
                    )
                except Exception:
                    pass
        return RootFinalizationResult(
            accepted=False,
            proof=verification_proof_text,
            verdict=str(
                certificate_status.get("verdict")
                or "root_finalization_certificate_rejected"
            ),
            helper_names=final_dependency_helper_names,
            route_contract_status=contract_status,
            verification_status=certificate_status,
        )
    replay_integrity_status: Dict[str, Any] = {}
    if dossier is not None:
        integrity_checker = getattr(dossier, "root_replay_integrity_status", None)
        if callable(integrity_checker):
            try:
                replay_integrity_status = dict(
                    integrity_checker(
                        replay_helpers=replay_helper_tuple,
                        helper_names=final_helper_names,
                        dependency_helper_names=final_dependency_helper_names,
                    )
                    or {}
                )
            except Exception as exc:
                replay_integrity_status = {
                    "ready": False,
                    "verdict": "root_finalization_replay_integrity_exception",
                    "exception_type": type(exc).__name__,
                    "exception_message": str(exc),
                }
            if replay_integrity_status and not bool(
                replay_integrity_status.get("ready")
            ):
                if record_attempt:
                    _increment_metric(dossier, "mini_root_finalization_blocked", 1)
                    _increment_metric(
                        dossier,
                        "mini_root_finalization_stale_helper_support",
                        1,
                    )
                    recorder = getattr(dossier, "record_attempt", None)
                    if callable(recorder):
                        try:
                            recorder(
                                phase=phase_text,
                                turn_index=int(turn_index or 0),
                                proof=proof_text,
                                helper_names=final_helper_names,
                                verdict=str(
                                    replay_integrity_status.get("verdict")
                                    or "root_finalization_stale_helper_support"
                                ),
                                metadata={
                                    "root_finalization_gate": True,
                                    "root_replay_integrity_status": dict(
                                        replay_integrity_status
                                    ),
                                    "root_verification_status": {
                                        **dict(certificate_status),
                                        "root_replay_integrity_status": dict(
                                            replay_integrity_status
                                        ),
                                    },
                                    "source_action_id": str(source_action_id or ""),
                                    "route_id": clean_route_id,
                                    "dependency_node_ids": list(
                                        clean_dependency_node_ids
                                    ),
                                    "dependency_helper_names": list(
                                        final_dependency_helper_names
                                    ),
                                    **dict(metadata or {}),
                                },
                            )
                        except Exception:
                            pass
                return RootFinalizationResult(
                    accepted=False,
                    proof=proof_text,
                    verdict=str(
                        replay_integrity_status.get("verdict")
                        or "root_finalization_stale_helper_support"
                    ),
                    helper_names=final_dependency_helper_names,
                    route_contract_status=contract_status,
                    verification_status={
                        **dict(certificate_status),
                        "root_replay_integrity_status": dict(
                            replay_integrity_status
                        ),
                    },
                )
    if dossier is not None:
        effective_require_route_contract = bool(require_route_contract)
        root_route_context_status: Dict[str, Any] = {}
        if clean_dependency_node_ids and not clean_route_id:
            effective_require_route_contract = True
        if final_dependency_helper_names and not clean_route_id:
            root_route_context_status = (
                _ready_root_assembly_contract_status_for_helper_support(
                    dossier,
                    target_statement=target_statement,
                    helper_names=final_dependency_helper_names,
                )
            )
            if bool(root_route_context_status.get("ready")):
                effective_require_route_contract = True
                clean_route_id = str(
                    root_route_context_status.get("route_id")
                    or root_route_context_status.get("created_route_id")
                    or ""
                ).strip()
                clean_dependency_node_ids = tuple(
                    str(item or "").strip()
                    for item in list(
                        root_route_context_status.get("dependency_node_ids")
                        or root_route_context_status.get("required_node_ids")
                        or ()
                    )
                    if str(item or "").strip()
                )
        needs_contract = bool(effective_require_route_contract or clean_route_id)
        if needs_contract:
            contract_status = _route_contract_status(
                dossier,
                route_id=clean_route_id,
                proof=proof_text,
                replay_helpers=replay_helper_tuple,
                phase=phase_text,
                turn_index=int(turn_index or 0),
                target_statement=target_statement,
                require_route_contract=effective_require_route_contract,
            )
            if root_route_context_status:
                contract_status = {
                    **dict(contract_status),
                    "ready_root_assembly_contract_status": dict(
                        root_route_context_status
                    ),
                }
            if bool(contract_status.get("ready")) and clean_route_id:
                support_status = _route_candidate_support_status(
                    dossier,
                    route_contract_status=contract_status,
                    helper_names=final_dependency_helper_names,
                )
                contract_status = {
                    **dict(contract_status),
                    "candidate_support_status": dict(support_status),
                }
                if not bool(support_status.get("ready")):
                    contract_status["ready"] = False
                    contract_status["verdict"] = str(
                        support_status.get("verdict")
                        or "route_candidate_helper_support_mismatch"
                    )
            if not bool(contract_status.get("ready")):
                if record_attempt:
                    _increment_metric(dossier, "mini_root_finalization_blocked", 1)
                    contract_verdict = str(contract_status.get("verdict") or "")
                    _increment_metric(
                        dossier,
                        (
                            "mini_root_finalization_support_mismatch"
                            if contract_verdict
                            in {
                                "route_candidate_helper_support_mismatch",
                                "route_candidate_missing_declared_helper_support",
                            }
                            else "mini_root_finalization_route_contract_not_ready"
                        ),
                        1,
                    )
                recorder = getattr(dossier, "record_attempt", None)
                if record_attempt and callable(recorder):
                    try:
                        recorder(
                            phase=phase_text,
                            turn_index=int(turn_index or 0),
                            proof=proof_text,
                            helper_names=final_helper_names,
                            verdict="root_finalization_contract_not_ready",
                            metadata={
                                "route_assembly_contract_status": contract_status,
                                "source_action_id": str(source_action_id or ""),
                                "route_id": clean_route_id,
                                "dependency_node_ids": list(clean_dependency_node_ids),
                                "dependency_helper_names": list(
                                    final_dependency_helper_names
                                ),
                                **dict(metadata or {}),
                            },
                        )
                    except Exception:
                        pass
                return RootFinalizationResult(
                    accepted=False,
                    proof=proof_text,
                    verdict=str(
                        contract_status.get("verdict")
                        or "root_finalization_contract_not_ready"
                    ),
                    helper_names=final_dependency_helper_names,
                    route_contract_status=contract_status,
                    verification_status=certificate_status,
                )

    if dossier is not None and persist_solution:
        if deadline_elapsed():
            return RootFinalizationResult(
                accepted=False,
                proof=proof_text,
                verdict="llm_turn_elapsed_budget_exhausted",
                helper_names=final_dependency_helper_names,
                route_contract_status=contract_status,
                verification_status=certificate_status,
            )
        if active_root_disproof_certificate_is_valid(
            dossier,
            reject_proof_conflicts=False,
        ):
            negative_certificate = (
                getattr(dossier, "root_disproof_certificate", None) or {}
            )
            _record_falsification_trust_boundary_conflict(
                dossier,
                certificate_hash=str(
                    negative_certificate.get("certificate_hash") or ""
                ),
            )
            dossier.root_disproof_certificate = None
            setattr(
                dossier,
                "session_failure_reason",
                "falsification_trust_boundary_conflict",
            )
            setattr(dossier, "session_failure_kind", "proof_disproof_conflict")
            if record_attempt:
                _increment_metric(dossier, "mini_root_finalization_blocked", 1)
                _increment_metric(
                    dossier,
                    "mini_root_finalization_proof_disproof_conflict",
                    1,
                )
            return RootFinalizationResult(
                accepted=False,
                proof=verification_proof_text,
                verdict="root_finalization_proof_disproof_conflict",
                helper_names=final_dependency_helper_names,
                route_contract_status=contract_status,
                verification_status=certificate_status,
            )
        graph = getattr(dossier, "proof_graph", None)
        # Root publication is one transaction across the dossier's solution,
        # cognition, and graph projections. Snapshot the complete graph state:
        # lifecycle reconciliation is allowed to inspect and update consumers
        # beyond the selected route, and a partial callback failure must not
        # leak any of those writes while reporting rejection.
        prior_graph_state = (
            copy.deepcopy(getattr(graph, "__dict__", {}))
            if graph is not None
            else None
        )
        prior_solution_snapshot = {
            "final_proof": copy.deepcopy(getattr(dossier, "final_proof", None)),
            "final_proof_hash": copy.deepcopy(
                getattr(dossier, "final_proof_hash", None)
            ),
            "final_replay_helpers": copy.deepcopy(
                getattr(dossier, "final_replay_helpers", [])
            ),
            "root_proof_certificate": copy.deepcopy(
                getattr(dossier, "root_proof_certificate", None)
            ),
            "_root_proof_finalization_receipts": copy.deepcopy(
                getattr(dossier, "_root_proof_finalization_receipts", set())
            ),
            "proof_ideas": copy.deepcopy(getattr(dossier, "proof_ideas", {})),
            "proof_lineage_events": copy.deepcopy(
                getattr(dossier, "proof_lineage_events", [])
            ),
            "proof_lineage_event_ids": copy.deepcopy(
                getattr(dossier, "proof_lineage_event_ids", set())
            ),
            "tool_metrics": copy.deepcopy(getattr(dossier, "tool_metrics", {})),
        }

        def restore_prior_solution() -> None:
            for field_name, prior_value in prior_solution_snapshot.items():
                setattr(dossier, field_name, copy.deepcopy(prior_value))
            if graph is None or prior_graph_state is None:
                return
            graph.__dict__.clear()
            graph.__dict__.update(copy.deepcopy(prior_graph_state))
        try:
            dossier.mark_solved(
                proof_text,
                replay_helpers=replay_helper_tuple,
                support_helper_names=final_dependency_helper_names,
                root_certificate_metadata={
                    "phase": phase_text,
                    "turn_index": int(turn_index or 0),
                    "source_action_id": str(source_action_id or ""),
                    "route_id": clean_route_id,
                    "dependency_node_ids": list(clean_dependency_node_ids),
                    "dependency_helper_names": list(final_dependency_helper_names),
                    "candidate_helper_names": list(final_helper_names),
                    "require_route_contract": bool(effective_require_route_contract),
                    "route_contract_status": dict(contract_status),
                    "verification_status": dict(certificate_status),
                    "verification_certificate": (
                        dict(verification_certificate)
                        if isinstance(verification_certificate, dict)
                        else {}
                    ),
                    "accepted_proof_hash": text_hash(verification_proof_text),
                    "artifact_proof_hash": text_hash(artifact_proof_text),
                    "artifact_proof_sanitized": (
                        verification_proof_text != artifact_proof_text
                    ),
                    "artifact_replay_helpers_sanitized": (
                        verification_replay_helper_tuple
                        != artifact_replay_helper_tuple
                    ),
                    **dict(metadata or {}),
                },
            )
            if deadline_elapsed():
                restore_prior_solution()
                return RootFinalizationResult(
                    accepted=False,
                    proof=proof_text,
                    verdict="llm_turn_elapsed_budget_exhausted",
                    helper_names=final_dependency_helper_names,
                    route_contract_status=contract_status,
                    verification_status=certificate_status,
                )
            _store_root_finalization_metadata(
                dossier,
                route_id=clean_route_id,
                dependency_node_ids=clean_dependency_node_ids,
                dependency_helper_names=final_dependency_helper_names,
                helper_names=final_helper_names,
                require_route_contract=effective_require_route_contract,
                contract_status=contract_status,
                verification_status=certificate_status,
                verification_certificate=verification_certificate,
            )
            if clean_route_id:
                close_route = getattr(
                    graph,
                    "mark_strategy_route_solved_by_kernel",
                    None,
                )
                if not callable(close_route) or not close_route(
                    clean_route_id,
                    proof=verification_proof_text,
                    dependency_node_ids=clean_dependency_node_ids,
                    turn_index=int(turn_index or 0),
                ):
                    raise RuntimeError(
                        "kernel-accepted root proof could not close its exact "
                        "strategy route"
                    )
                reconcile_lifecycle = getattr(
                    dossier,
                    "reconcile_proof_idea_graph_statuses",
                    None,
                )
                if callable(reconcile_lifecycle):
                    reconcile_lifecycle()
        except Exception as exc:
            restore_prior_solution()
            _increment_metric(dossier, "mini_root_finalization_blocked", 1)
            return RootFinalizationResult(
                accepted=False,
                proof=proof_text,
                verdict="root_finalization_exception",
                helper_names=final_dependency_helper_names,
                route_contract_status=contract_status,
                verification_status=certificate_status,
                exception_type=type(exc).__name__,
                exception_message=str(exc),
            )
    if dossier is not None and record_attempt:
        try:
            dossier.record_attempt(
                phase=phase_text,
                turn_index=int(turn_index or 0),
                proof=proof_text,
                helper_names=final_dependency_helper_names,
                verdict="solved",
                metadata={
                    "root_finalization_gate": True,
                    "replay_helper_names": list(final_helper_names),
                    "source_action_id": str(source_action_id or ""),
                    "route_id": clean_route_id,
                    "dependency_node_ids": list(clean_dependency_node_ids),
                    "dependency_helper_names": list(final_dependency_helper_names),
                    "route_assembly_contract_status": contract_status,
                    "root_verification_status": dict(certificate_status),
                    **dict(metadata or {}),
                },
            )
        except Exception:
            pass
    if dossier is not None and record_attempt:
        _increment_metric(dossier, "mini_root_finalization_accepted", 1)
        if bool(require_verification_certificate):
            _increment_metric(
                dossier,
                "mini_root_finalization_certificate_accepted",
                1,
            )
    try:
        if proof_state is not None:
            marker = getattr(proof_state, "mark_root_solved", None)
            if callable(marker):
                try:
                    marker()
                except Exception:
                    pass
            sync = getattr(proof_state, "sync_to_graph", None)
            if callable(sync) and dossier is not None:
                try:
                    sync(dossier, phase=phase_text, turn_index=int(turn_index or 0))
                except Exception:
                    pass
    except Exception as exc:
        if dossier is not None:
            _increment_metric(dossier, "mini_root_finalization_blocked", 1)
        return RootFinalizationResult(
            accepted=False,
            proof=proof_text,
            verdict="root_finalization_exception",
            helper_names=final_dependency_helper_names,
            route_contract_status=contract_status,
            verification_status=certificate_status,
            exception_type=type(exc).__name__,
            exception_message=str(exc),
        )

    return RootFinalizationResult(
        accepted=True,
        proof=proof_text,
        verdict="root_finalization_accepted",
        helper_names=final_dependency_helper_names,
        route_contract_status=contract_status,
        verification_status=certificate_status,
    )


def finalize_root_solution(
    *,
    dossier: Any,
    proof_state: Optional[Any] = None,
    proof: str,
    replay_helpers: Iterable[str] = (),
    helper_names: Iterable[str] = (),
    phase: str = "",
    turn_index: int = 0,
    source_action_id: str = "",
    route_id: str = "",
    dependency_node_ids: Iterable[str] = (),
    dependency_helper_names: Iterable[str] = (),
    target_statement: str = "",
    require_route_contract: bool = False,
    verification_certificate: Optional[Dict[str, Any]] = None,
    require_verification_certificate: bool = False,
    record_attempt: bool = True,
    persist_solution: bool = True,
    metadata: Optional[Dict[str, Any]] = None,
    deadline_exhausted: Optional[Callable[[], bool]] = None,
) -> RootFinalizationResult:
    """Apply root finalization as one deadline-aware dossier/state commit."""

    transaction = DeadlineMutationTransaction(
        deadline_exhausted=deadline_exhausted,
        dossier=dossier,
        proof_state=proof_state,
        label="root_finalization",
    )

    def cancelled(verdict: str = "llm_turn_elapsed_budget_exhausted") -> RootFinalizationResult:
        return RootFinalizationResult(
            accepted=False,
            proof=sanitize_lean_artifact_text(str(proof or "")),
            verdict=verdict,
        )

    with transaction:
        if not transaction.can_mutate():
            return cancelled()
        result = _finalize_root_solution_impl(
            dossier=dossier,
            proof_state=proof_state,
            proof=proof,
            replay_helpers=replay_helpers,
            helper_names=helper_names,
            phase=phase,
            turn_index=turn_index,
            source_action_id=source_action_id,
            route_id=route_id,
            dependency_node_ids=dependency_node_ids,
            dependency_helper_names=dependency_helper_names,
            target_statement=target_statement,
            require_route_contract=require_route_contract,
            verification_certificate=verification_certificate,
            require_verification_certificate=require_verification_certificate,
            record_attempt=record_attempt,
            persist_solution=persist_solution,
            metadata=metadata,
            deadline_exhausted=deadline_exhausted,
        )
        if result.accepted and persist_solution and dossier is not None:
            if transaction.enabled:
                transaction.add_participant(
                    _RootProofFinalizationReceiptParticipant(dossier)
                )
            else:
                dossier.record_root_proof_finalization_receipt()
        if not transaction.can_mutate():
            return cancelled()
    if transaction.enabled and not transaction.committed:
        return cancelled(
            "llm_turn_elapsed_budget_exhausted"
            if transaction.deadline_won
            else "deadline_mutation_commit_failed"
        )
    return result
