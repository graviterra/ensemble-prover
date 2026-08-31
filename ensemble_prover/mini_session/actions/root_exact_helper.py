"""RootExactHelperAction — wraps `_try_proof_state_root_exact_helper`.

Single-shot attempt to close the root with ``by exact <helper_name>``.
Cheap (~one Lean check). Used after a helper is verified that the
graph believes is alpha-equal to the root statement.
"""

from __future__ import annotations

import time
from typing import Any, ClassVar, FrozenSet

from ensemble_prover.proof_dossier import helper_decl_name
from ensemble_prover.root_finalization import (
    RootFinalizationCandidate,
    root_verification_certificate,
)

from ..action import MiniOutcome


class RootExactHelperAction:
    id: str = "root_exact_helper"
    priority: int = 8
    cost_estimate_s: float = 2.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier"})

    def __init__(
        self,
        *,
        helper_name: str = "",
        timeout_s: float = 10.0,
    ) -> None:
        self.helper_name = str(helper_name or "").strip()
        self.timeout_s = float(timeout_s or 0.0)

    def is_applicable(self, session: Any) -> bool:
        if self.timeout_s <= 0.0 or not self.helper_name:
            return False
        if session.dossier is None or session.proof_state is None or session.lean is None:
            return False
        # Helper must exist on the dossier.
        has_helper = getattr(session.dossier, "has_helper", None)
        if callable(has_helper) and not has_helper(self.helper_name):
            return False
        return True

    async def run(self, session: Any) -> MiniOutcome:
        from ensemble_prover.proof_state_executor import _try_proof_state_root_exact_helper

        started = time.monotonic()
        ok, proof, record = await _try_proof_state_root_exact_helper(
            conv=session.conv,
            lean=session.lean,
            dossier=session.dossier,
            proof_state=session.proof_state,
            helper_name=self.helper_name,
            turn=int(getattr(session, "iteration", 0)),
            timeout_s=self.timeout_s,
        )
        cost = time.monotonic() - started
        replay_helpers = (
            tuple(session.dossier.verified_helper_blocks())
            if ok and proof and getattr(session, "dossier", None) is not None
            else ()
        )
        route_status = dict(record.get("route_assembly_contract_status") or {})
        route_helper_names = tuple(
            str(name or "").strip()
            for name in [
                route_status.get("helper_name"),
                *list(route_status.get("helper_names") or []),
            ]
            if str(name or "").strip()
        )
        helper_names = route_helper_names or tuple(
            name
            for block in replay_helpers
            for name in [helper_decl_name(block)]
            if name
        )
        replay_helpers = tuple(
            block
            for block in replay_helpers
            if not helper_names or (helper_decl_name(block) or "") in set(helper_names)
        )
        return MiniOutcome(
            action_id=self.id,
            solved=bool(ok),
            proof=proof if ok and proof else None,
            helpers_added=(self.helper_name,) if ok else (),
            progress=bool(ok),
            cost_seconds=cost,
            root_candidate=(
                RootFinalizationCandidate(
                    proof=proof or "",
                    replay_helpers=replay_helpers,
                    helper_names=helper_names,
                    phase="proof_state_root_exact_helper",
                    turn_index=int(getattr(session, "iteration", 0)),
                    source_action_id=self.id,
                    route_id=str(route_status.get("route_id") or ""),
                    dependency_node_ids=tuple(
                        str(node_id or "").strip()
                        for node_id in list(
                            route_status.get("dependency_node_ids")
                            or route_status.get("required_node_ids")
                            or []
                        )
                        if str(node_id or "").strip()
                    ),
                    target_statement=str(
                        getattr(session.dossier, "root_statement", "")
                        or getattr(getattr(session, "conv", None), "goal_statement", "")
                        or ""
                    ),
                    require_route_contract=True,
                    verification_certificate=root_verification_certificate(
                        accepted=True,
                        proof=proof or "",
                        phase="proof_state_root_exact_helper",
                        turn_index=int(getattr(session, "iteration", 0)),
                        target_statement=str(
                            getattr(session.dossier, "root_statement", "")
                            or getattr(
                                getattr(session, "conv", None),
                                "goal_statement",
                                "",
                            )
                            or ""
                        ),
                        replay_helpers=replay_helpers,
                        helper_names=helper_names,
                        source=self.id,
                    ),
                    metadata={
                        "root_finalization_already_applied": True,
                        "route_assembly_contract_status": route_status,
                    },
                )
                if ok and proof
                else None
            ),
            metadata={
                "helper_name": self.helper_name,
                "verdict": str(record.get("verdict") or ""),
                "replay_helpers": list(replay_helpers),
                "helper_names": list(helper_names),
                "root_finalization_already_applied": bool(ok and proof),
            },
        )
