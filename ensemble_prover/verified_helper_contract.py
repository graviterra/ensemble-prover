"""Fresh typed evidence for accepted helpers with ambiguous surface binders."""

from __future__ import annotations

import copy
import asyncio
import logging
import time
from typing import Any, Callable, Mapping, Sequence

from .contract_identity import (
    has_lean_contract_identity,
    make_lean_contract_binder_evidence_receipt,
    make_lean_contract_evidence_receipt,
)
from .lean_runner import LeanStatementContractAnalysis
from .proof_graph import graph_statement_contract_ambiguities
from .proof_dossier import canonical_dossier_statement_key


_LOGGER = logging.getLogger(__name__)


class _ContractAnalysisCancelled(BaseException):
    """Preserve explicit adapter cancellation across result-only watchdogs."""


async def analyze_verified_helper_contract(
    lean: Any,
    statement: str,
    *,
    preamble: str,
    context: Sequence[str],
    environment_hash: str,
    timeout_s: float,
    context_is_current: Callable[[], bool] = lambda: True,
) -> Mapping[str, Any]:
    """Enrich a proved declaration; incomplete evidence never relaxes policy.

    Call only after body verification. Known surface sorts avoid another Lean
    operation. Failure is advisory, cancellation propagates, and callers retain
    ownership of their acceptance deadline and publication transaction.
    """

    analyzer = getattr(lean, "analyze_statement_contracts", None)
    if (
        not callable(analyzer)
        or timeout_s <= 0
        or not graph_statement_contract_ambiguities(statement)
        or not context_is_current()
    ):
        return {}
    try:
        from .mini_formal_state_search import _run_serialized_lean_operation

        deadline = time.monotonic() + timeout_s

        async def analyze() -> Any:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return (), "contract analysis budget exhausted", 1
            try:
                return await analyzer(
                    [statement],
                    preamble_override="\n\n".join(
                        part for part in (preamble, *context) if part
                    ),
                    timeout_s=remaining,
                )
            except asyncio.CancelledError as exc:
                raise _ContractAnalysisCancelled from exc

        # Use the existing Lean lease/watchdog: a cancellation-resistant tail
        # keeps its lease until it stops, and cannot publish a late receipt.
        # Lean owns its process deadline; the outer guard includes teardown
        # headroom instead of racing the process at the same instant.
        analyses, _output, returncode = await _run_serialized_lean_operation(
            lean, analyze, operation_timeout_s=timeout_s,
            admission_timeout_s=timeout_s,
        )
        analysis = analyses[0] if len(analyses) == 1 else None
        if (
            returncode != 0
            or not isinstance(analysis, LeanStatementContractAnalysis)
            or not has_lean_contract_identity(analysis.structural_identity)
            or not analysis.binder_sorts
            or any(sort not in {"proof", "data"} for sort in analysis.binder_sorts)
            or len(analysis.binder_types) != len(analysis.binder_sorts)
            or any(not isinstance(value, str) or not value.strip()
                   for value in analysis.binder_types)
            or analysis.binder_sorts.count("proof") != len(analysis.proof_binder_types)
            or any(not isinstance(value, str) or not value.strip()
                   for value in analysis.proof_binder_types)
            or not context_is_current()
        ):
            return {}
    except _ContractAnalysisCancelled as exc:
        raise asyncio.CancelledError from exc
    except Exception:
        # A transient analysis failure cannot erase a completed body check.
        # The empty result keeps conservative visibility; it is not cached.
        _LOGGER.debug("Accepted helper binder analysis unavailable", exc_info=True)
        return {}
    return {
        "contract_identity": analysis.structural_identity,
        "contract_display_statement": analysis.display_type,
        "contract_binder_sorts": analysis.binder_sorts,
        "contract_proof_binder_types": analysis.proof_binder_types,
        "_contract_identity_statement": statement,
        "_verification_environment_hash": environment_hash,
    }


def refresh_verified_helper_contract(dossier: Any, helper: Any, fields: Mapping[str, Any]) -> bool:
    """Attach fresh same-environment evidence through the normal import gate."""

    if not fields:
        return False
    incoming = copy.deepcopy(helper)
    for name in (
        "contract_identity", "contract_display_statement",
        "contract_binder_sorts", "contract_proof_binder_types",
    ):
        value = fields[name]
        setattr(incoming, name, list(value) if isinstance(value, tuple) else value)
    key = canonical_dossier_statement_key(fields["_contract_identity_statement"])
    environment = str(fields["_verification_environment_hash"])
    incoming.contract_identity_statement_key = key
    incoming.contract_identity_environment_hash = environment
    incoming.contract_identity_evidence_receipt = make_lean_contract_evidence_receipt(
        incoming.contract_identity, key, environment,
    )
    incoming.contract_binder_evidence_receipt = make_lean_contract_binder_evidence_receipt(
        incoming.contract_identity, key, environment,
        tuple(incoming.contract_binder_sorts), tuple(incoming.contract_proof_binder_types),
    )
    return bool(dossier.refresh_imported_verified_helper_evidence(helper.name, incoming))
