"""Bounded historical Lean rejection feedback for later root assembly."""

from __future__ import annotations

import hashlib
import json
from typing import Any, Mapping, Sequence

MAX_RECEIPTS = 3
MAX_PROOF_CHARS = 24000
MAX_DIAGNOSTIC_CHARS = 16000


def _valid_context(context: Any) -> bool:
    return (isinstance(context, dict)
            and set(context) == {"target", "model_preamble", "checker_preamble", "environment", "answer_policy"}
            and isinstance(context["target"], str) and 0 < len(context["target"]) <= 24000
            and all(isinstance(context[key], str) and len(context[key]) == 64
                    and all(c in "0123456789abcdef" for c in context[key])
                    for key in ("model_preamble", "checker_preamble", "environment"))
            and isinstance(context["answer_policy"], list) and len(context["answer_policy"]) == 4
            and all(value is None or type(value) is bool for value in context["answer_policy"]))


def _digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()).hexdigest()


def closure_context(conv: Any, lean: Any) -> dict[str, Any]:
    from .mini_recursive import _recursive_runtime_component_identity

    current = getattr(lean, "current_generation", None)
    if callable(current):
        lean = current()
    return {
        "target": str(getattr(conv, "goal_statement", "") or ""),
        "model_preamble": _digest(str(getattr(conv, "preamble", "") or "")),
        "checker_preamble": _digest(str(getattr(conv, "lean_preamble", "") or "")),
        "environment": _digest(_recursive_runtime_component_identity(lean)),
        "answer_policy": [getattr(conv, key, None) for key in (
            "suppress_solution_placeholders", "opaque_mode",
            "allow_official_answer_visibility", "official_answer_payload_present",
        )],
    }


def bounded_receipts(value: Any) -> list[dict[str, Any]]:
    """Load advisory records without restoring proof or failure authority."""
    if not isinstance(value, list):
        return []
    records = []
    for item in value[-MAX_RECEIPTS:]:
        if not isinstance(item, dict):
            continue
        context = item.get("context")
        helpers = item.get("helper_sources")
        names = item.get("helper_names")
        proof, diagnostic = item.get("proof"), item.get("diagnostic")
        if (not _valid_context(context) or not isinstance(helpers, list)
                or not isinstance(names, list) or len(names) != len(helpers)
                or not all(isinstance(name, str) and len(name) <= 512 for name in names)
                or len(helpers) > 512 or not all(isinstance(h, str) and len(h) == 64 for h in helpers)
                or not isinstance(proof, str) or not 0 < len(proof) <= MAX_PROOF_CHARS
                or not isinstance(diagnostic, str) or not 0 < len(diagnostic) <= MAX_DIAGNOSTIC_CHARS
                or len(json.dumps(context, ensure_ascii=False)) > 32000):
            continue
        record = {"context": context, "helper_sources": helpers, "helper_names": names, "proof": proof,
                  "diagnostic": diagnostic, "diagnostic_truncated": bool(item.get("diagnostic_truncated"))}
        if item.get("receipt_id") != _digest(record):
            continue
        records.append({**record, "receipt_id": item["receipt_id"]})
    return records


def capture_checked_failure(*, dossier: Any, conv: Any, lean: Any, proof: str,
                            helpers: Sequence[str], verdict: Any, checked_target: str) -> None:
    """Remember a completed rejected candidate, never a claim's falsity."""
    if dossier is None or checked_target != str(getattr(conv, "goal_statement", "") or ""):
        return
    if checked_target != str(getattr(dossier, "root_statement", "") or ""):
        return
    if getattr(verdict, "primary_source", "submitted") != "submitted":
        return
    primary = getattr(verdict, "primary_result", None)
    feedback = getattr(verdict, "feedback_result", None)
    if (bool(getattr(verdict, "accepted", False)) or bool(getattr(primary, "ok", False))
            or feedback is None or bool(getattr(feedback, "ok", False))
            or bool(getattr(getattr(primary, "parsed", None), "infra_failure", False))
            or bool(getattr(getattr(feedback, "parsed", None), "infra_failure", False))):
        return
    if any(getattr(result, "parsed", None) is None
           or getattr(result, "returncode", None) not in (0, 1) for result in (primary, feedback)):
        return
    output = str(getattr(feedback, "output", "") or "")
    if not output or not isinstance(proof, str) or not 0 < len(proof) <= MAX_PROOF_CHARS:
        return
    from .proof_dossier import helper_decl_name

    helper_sources = [_digest(str(block)) for block in helpers]
    helper_names = [helper_decl_name(str(block)) or "" for block in helpers]
    if len(helper_sources) > 512:
        return
    record = {"context": closure_context(conv, lean), "helper_sources": helper_sources, "helper_names": helper_names,
              "proof": proof, "diagnostic": output[:MAX_DIAGNOSTIC_CHARS],
              "diagnostic_truncated": len(output) > MAX_DIAGNOSTIC_CHARS}
    record["receipt_id"] = _digest(record)
    merge_feedback(dossier, [record])


def merge_feedback(dossier: Any, receipts: Any) -> None:
    records = bounded_receipts(getattr(dossier, "checked_failure_feedback", []))
    for record in bounded_receipts(receipts):
        records = [old for old in records if old["receipt_id"] != record["receipt_id"]]
        records.append(record)
    dossier.checked_failure_feedback = records[-MAX_RECEIPTS:]


def render_closure_feedback(*, dossier: Any, conv: Any, lean: Any,
                            helpers: Sequence[str]) -> str:
    from .proof_dossier import _prompt_safe_lean_diagnostic_text, helper_decl_name
    from .proof_dossier import effective_solution_placeholder_suppression

    receipts = bounded_receipts(getattr(dossier, "checked_failure_feedback", []))
    if not receipts:
        return ""
    context = closure_context(conv, lean)
    current_sources = [_digest(str(block)) for block in helpers]
    current_names: dict[str, set[str]] = {}
    for block, digest in zip(helpers, current_sources):
        name = helper_decl_name(str(block)) or ""
        if name:
            current_names.setdefault(name, set()).add(digest)

    def helpers_match(record: Mapping[str, Any]) -> bool:
        cursor = iter(current_sources)
        return (all(any(current == old for current in cursor) for old in record["helper_sources"])
                and all(not name or current_names.get(name) == {digest}
                        for name, digest in zip(record["helper_names"], record["helper_sources"])))

    matching = [r for r in receipts if r["context"] == context and helpers_match(r)]
    if not matching:
        return ""
    record = matching[-1]
    redact = effective_solution_placeholder_suppression(**{
        key: getattr(conv, key, None) for key in (
            "suppress_solution_placeholders", "opaque_mode",
            "allow_official_answer_visibility", "official_answer_payload_present",
        )
    })
    def safe(text: str) -> str:
        return _prompt_safe_lean_diagnostic_text(
            text, limit=MAX_PROOF_CHARS, preserve_line_breaks=True,
            redact_solution_refs=redact,
        )
    return ("Previous root-assembly candidate rejected by Lean in this target and environment. "
            "Additional verified helpers may now be available. This is historical code feedback, "
            "not a refutation of the mathematical claim. Research advice remains unverified: if its "
            "code repeats the identifiers or steps rejected below, correct or recheck that code; "
            "do not treat claims that it is kernel-ready as verification.\n"
            + "Rejected proof (JSON string):\n" + json.dumps(safe(record["proof"]), ensure_ascii=False)
            + "\nLean diagnostic" + (" (truncated)" if record["diagnostic_truncated"] else "")
            + " (JSON string):\n" + json.dumps(safe(record["diagnostic"]), ensure_ascii=False))
