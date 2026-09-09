"""Fresh Lean evidence for stored helpers excluded by replay-context policy.

Replay provenance is conservative: a name need not occur in the proof for its
instances or attributes to matter. Only an accepted replay may reduce that
context. Conditional lemmas are applied to the full active target, never
converted into unconditional facts by a syntactic premise matcher.
"""

from __future__ import annotations

import copy
import json
import time
from dataclasses import asdict, dataclass
from types import SimpleNamespace
from typing import Any, Callable

from .proof_dossier import ProofDossier, helper_decl_name, text_hash


@dataclass(frozen=True)
class HelperContextRepairResult:
    repaired_names: tuple[str, ...] = ()
    proof: str = ""
    replay_helpers: tuple[str, ...] = ()
    retryable: bool = False


def helper_context_repair_key(dossier: ProofDossier, preamble: str, target: str) -> str:
    """Bind a dispatch's attempted repair to its exact evidence and frame."""
    return text_hash(json.dumps({
        "preamble": preamble,
        "target": target,
        "environment": dossier.current_lean_environment_hash,
        "helpers": [asdict(helper) for helper in dossier.verified_helpers.values()],
    }, sort_keys=True))


async def repair_verified_helper_context(
    *,
    dossier: ProofDossier,
    lean: Any,
    preamble: str,
    target_statement: str = "",
    timeout_s: float = 10.0,
    max_total_seconds: float = 60.0,
    max_helpers: int = 16,
    turn_index: int = 0,
    publication_guard: Callable[[], None] | None = None,
) -> HelperContextRepairResult:
    """Repair excluded foundations and try a checked conditional composition.

    The caller owns dispatch publication and root finalization. The returned
    proof is a candidate checked against exactly ``target_statement``; this
    function does not mark a root or any conditional premise as proved.
    """
    started = time.monotonic()
    repaired: list[str] = []
    retryable = False
    if lean is None or timeout_s <= 0 or max_total_seconds <= 0:
        return HelperContextRepairResult()
    dossier.verified_helper_blocks()

    def remaining() -> float:
        return max(0.0, min(timeout_s, max_total_seconds - (time.monotonic() - started)))

    def integrity(names: list[str]) -> bool:
        status = dossier.root_replay_integrity_status(helper_names=names, refresh_quality=False)
        return bool(status.get("ready")) and all(
            helper.source_hash == text_hash(helper.source)
            and helper.verification_environment_hash == dossier.current_lean_environment_hash
            for name in status.get("checked_helper_names", ())
            for helper in [dossier.verified_helpers[name]]
        )

    def publish_guard(expected_key: str) -> None:
        if publication_guard is not None:
            publication_guard()
        if helper_context_repair_key(dossier, preamble, target_statement) != expected_key:
            raise ValueError("helper evidence changed during context repair")

    def retryable_check(result: Any) -> bool:
        from .lean_runner import _execution_ended_without_complete_contract_output

        return bool(getattr(getattr(result, "parsed", None), "infra_failure", False)) or (
            bool(result.ok) and getattr(result, "axiom_audit_ok", None) is None
        ) or (
            _execution_ended_without_complete_contract_output(SimpleNamespace(
                returncode=getattr(result, "returncode", 0 if result.ok else 1),
                output=result.output, backend="",
            ))
        )

    # Use original declaration names and exact sources, with support closures.
    # A textual scan only proposes a context; Lean decides whether it suffices.
    attempted = 0
    for name in list(dossier.verified_helpers):
        visible = {helper_decl_name(block) for block in dossier.verified_helper_blocks(refresh_quality=False)}
        helper = dossier.verified_helpers[name]
        if (
            name in visible
            or not dossier.is_verified_helper_context_visible(helper)
            or not helper.replay_context_names
            or not integrity([name])
        ):
            continue
        if attempted >= max_helpers or remaining() <= 0:
            retryable = True
            break
        supports = list(dict.fromkeys([
            *helper.support_names,
            *dossier._referenced_verified_helper_names(helper.source, skip=name),
        ]))
        if not set(supports).issubset(visible):
            continue
        blocks = dossier.root_replay_helper_closure(
            replay_helpers=[dossier.verified_helpers[support].source for support in supports],
            refresh_quality=False,
        ) if supports else []
        names = [helper_decl_name(block) for block in blocks]
        if not set(supports).issubset(names) or not set(names).issubset(visible):
            continue
        dossier.validate_helper_context(blocks)
        expected_key = helper_context_repair_key(dossier, preamble, target_statement)
        check_timeout = remaining()
        if check_timeout <= 0:
            retryable = True
            break
        attempted += 1
        result = await lean.check(
            "True", "by trivial", [*blocks, helper.source],
            preamble_override=preamble, timeout_s=check_timeout,
            check_kind="helper_context_repair",
        )
        publish_guard(expected_key)
        if not result.ok or getattr(result, "axiom_audit_ok", None) is not True:
            retryable = retryable or retryable_check(result)
            continue
        receipt = {
            "source_hash": helper.source_hash,
            "verification_environment_hash": dossier.current_lean_environment_hash,
            "preamble_hash": text_hash(preamble),
            "previous_replay_context_names": list(helper.replay_context_names),
            "previous_replay_context_source_hashes": dict(helper.replay_context_source_hashes),
            "replay_context_names": names,
            "replay_context_source_hashes": {
                dep: dossier.verified_helpers[dep].source_hash for dep in names
            },
            "axiom_audit_ok": True,
        }
        helper.replay_context_repair_receipts.append(copy.deepcopy(receipt))
        helper.replay_context_names = list(names)
        helper.replay_context_source_hashes = dict(receipt["replay_context_source_hashes"])
        dossier.record_attempt(
            phase="helper_context_repair", turn_index=turn_index,
            proof=helper.source, helper_names=[name],
            verdict="helper_context_repaired", metadata=receipt,
        )
        repaired.append(name)

    if repaired:
        dossier._refresh_verified_helper_quality()
        dossier._refresh_verified_helper_statement_aliases()
        dossier.reconcile_verified_facts(trigger="helper_context_repair")

    outcome = HelperContextRepairResult(
        repaired_names=tuple(repaired), retryable=retryable or remaining() <= 0,
    )
    conditional = [
        helper for helper in dossier.verified_helpers.values()
        if helper.render_policy == "advisory_requires_unproved_premise"
        and not helper.visibility_policy
    ]
    if not target_statement or not conditional or remaining() <= 0:
        return outcome
    # Restrict the search to verified constructive evidence and conditional
    # reducers. Refutations, route-only evidence and root aliases stay excluded.
    allowed = {
        helper.name for helper in dossier.verified_helpers.values()
        if (dossier.is_verified_helper_context_visible(helper) or helper in conditional)
        and not helper.visibility_policy
    }
    if len(allowed) > 64 or not integrity(list(allowed)):
        return outcome
    blocks = dossier.root_replay_helper_closure(replay_helpers=[
        helper.source for helper in dossier.verified_helpers.values() if helper.name in allowed
    ])
    names = [helper_decl_name(block) for block in blocks]
    if set(names) != allowed:
        return outcome
    dossier.validate_helper_context(blocks)
    # Lean introduces the target's binders and checks every premise obligation.
    # Keeping the implication in its original type avoids global promotion.
    proof = "by\n  intros\n  solve_by_elim (config := { maxDepth := 6 }) only [*, " + ", ".join(names) + "]"
    expected_key = helper_context_repair_key(dossier, preamble, target_statement)
    check_timeout = remaining()
    if check_timeout <= 0:
        return HelperContextRepairResult(tuple(repaired), retryable=True)
    result = await lean.check(
        target_statement, proof, blocks, preamble_override=preamble,
        timeout_s=check_timeout, check_kind="helper_context_conditional_application",
    )
    publish_guard(expected_key)
    if not result.ok or getattr(result, "axiom_audit_ok", None) is not True:
        return HelperContextRepairResult(
            tuple(repaired), retryable=retryable or retryable_check(result),
        )
    return HelperContextRepairResult(tuple(repaired), proof, tuple(blocks))
