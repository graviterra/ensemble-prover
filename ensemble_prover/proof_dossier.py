"""Structured run-local evidence and status for ensemble theorem search.

``ProofDossier`` records verified helpers, attempted proof fragments, scratch
checks, provenance, and root status. It is the evidence boundary shared by the
scheduler, proof graph, repair paths, checkpoints, and exporter; a chat
transcript alone never establishes proof acceptance.
"""

from __future__ import annotations

import copy
import hashlib
import json
import re
import secrets
import unicodedata
from dataclasses import asdict, dataclass, field, replace
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Set, Tuple

from .state_data import clone_json_value
from .falsification_cursor_identity import (
    FALSIFICATION_CURSOR_TARGET_SCHEMA,
    GRAPH_PLAN_CURSOR_SCHEMA,
    RIGHT_PI_LEGACY_PLAN_CURSOR_SCHEMA,
    RIGHT_PI_OLDER_PLAN_CURSOR_SCHEMA,
    RIGHT_PI_PLAN_CURSOR_SCHEMA,
    RIGHT_PI_PREVIOUS_PLAN_CURSOR_SCHEMA,
    RIGHT_PI_RECENT_PLAN_CURSOR_SCHEMA,
    right_pi_recipe_repair_disposition_is_valid,
)
from .contract_identity import (
    has_lean_contract_identity,
    lean_contract_evidence_receipt_matches,
    make_lean_contract_evidence_receipt,
    parse_lean_contract_identity,
)
from .helper_quality import verified_helper_admission_quality
from .lean_artifact_sanitize import (
    sanitize_lean_artifact_text,
    sanitize_lean_artifact_texts,
)
from .lean_syntax import split_lean_top_level_implications
from .proof_graph import (
    ProofGraph,
    _ROUTE_DEPENDENCY_EDGE_KINDS,
    _graph_binder_group_chunks,
    _helper_decl_header as graph_helper_decl_header,
    _graph_metadata_raw_lean_identities,
    _graph_statement_is_context_bare_prop_atom,
    graph_node_bound_contract_identity,
    graph_helper_answer_safety_receipt,
    graph_root_equivalent_suppression_decision,
    graph_statement_closed_data_requirements,
    graph_statement_closed_premises,
    graph_statement_contract_ambiguities,
    graph_statement_has_circular_premise,
    graph_statement_nonproof_parameter_profile,
    graph_statement_premises_and_conclusion,
    graph_statement_is_root_bridge,
    graph_statement_root_equivalent,
    graph_statement_non_theorem_reason,
    graph_statement_is_executable,
    graph_statement_key,
    graph_statement_leading_contract,
    helper_decl_body,
    helper_decl_kind,
    helper_decl_name as graph_helper_decl_name,
    helper_decl_statement,
)
from .proof_lineage import (
    ProofIdeaBranchProvenance,
    ProofIdeaClaimIntent,
    ProofIdeaClaimResolution,
    ProofIdeaConsumerBinding,
    ProofIdeaContextEvidence,
    ProofIdeaGlobalContextProjection,
    ProofIdeaContextProjection,
    ProofIdeaContextResolution,
    ProofIdeaExecutionScope,
    ProofIdeaObservation,
    ProofIdeaRecord,
    ProofIdeaStatusTransition,
    ProofLineageEnvelope,
    lineage_event_identity,
    proof_idea_identity,
    stable_identity,
    strategy_lineage_identity,
    structural_statement_identity,
)
from .utils import (
    _lean_lexical_skip_end,
    canonical_lean_identifier,
    fresh_lean_alternative_identifier,
    has_materialization_incompatible_placeholders,
    has_placeholder_tactics,
    rename_lean_identifier,
)


class StaleProofIdeaContextProjectionError(ValueError):
    """A resolved proof-idea packet changed before it could be projected."""


_AUTHENTICATED_EXECUTION_RESTORE = object()


_MATERIALIZED_SOLUTION_DECL_RE = re.compile(
    r"(?m)^\s*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?:def|abbrev|theorem|lemma|axiom)\s+"
    r"(?:«[^»]*_solution[^»]*»|[A-Za-z_][A-Za-z0-9_'.]*_solution[A-Za-z0-9_'.]*)"
    r"\b[^\n]*(?::=|where\b)"
)
_SPECULATIVE_COUNTEREXAMPLE_TEXT_RE = re.compile(
    r"(?<![A-Za-z0-9])(?:counterexamples?|counter-examples?|"
    r"disprov(?:e|es|ed|ing)|refut(?:e|es|ed|ing|ation)|"
    r"falsif(?:y|ies|ied|ying))(?![A-Za-z0-9])",
    re.IGNORECASE,
)
_COUNTEREXAMPLE_EXCLUSION_TEXT_RE = re.compile(
    r"(?<![A-Za-z0-9])(?:no|not|without)\s+counterexamples?"
    r"(?![A-Za-z0-9])|"
    r"(?<![A-Za-z0-9])(?:exclude(?:s|d|ing)?|rule(?:s|d)?\s+out)\s+"
    r"counterexamples?(?![A-Za-z0-9])|"
    r"(?<![A-Za-z0-9])no_counterexamples?(?![A-Za-z0-9])|"
    r"(?<![A-Za-z0-9])counterexamples?[_\s]+"
    r"(?:free|exclu(?:de|des|ded|ding|sion)|impossible)"
    r"(?![A-Za-z0-9])",
    re.IGNORECASE,
)
_SPECULATIVE_COUNTEREXAMPLE_FAILURE_VERDICTS = frozenset(
    {"tactic_rejected", "claim_llm_failed", "claim_exhausted"}
)
_SOLUTION_REF_RE = re.compile(
    r"(?:«[^»]*_solution[^»]*»|"
    r"[A-Za-z_][A-Za-z0-9_'.]*_solution[A-Za-z0-9_'.]*|"
    r"putnam_[A-Za-z0-9_'.]*\.\s*(?:solution[A-Za-z0-9_'.]*|«solution»))"
)
_PUTNAM_SOLUTION_REF_RE = re.compile(
    r"(?:putnam_[A-Za-z0-9_'.]*_solution[A-Za-z0-9_'.]*|"
    r"putnam_[A-Za-z0-9_'.]*\.\s*(?:solution[A-Za-z0-9_'.]*|«solution»))"
)
_SOLUTION_EQUIVALENCE_HINT_RE = re.compile(r"(?:↔|<->|\bIff\b)")
_GENERATED_HELPER_REFERENCE_RE = re.compile(
    r"(?<![A-Za-z0-9_'.])"
    r"((?:mini|obligation|bridge|lemma)_[A-Za-z0-9_'.]*)"
    r"(?![A-Za-z0-9_'])"
)
_ROOT_EQUIVALENCE_PLACEHOLDER_STATEMENTS = frozenset({
    "",
    "True",
    "False",
    "p",
    "q",
    "r",
    "P",
    "Q",
    "R",
    "Root",
})
_DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE = {
    "(": ")",
    "[": "]",
    "{": "}",
    "⦃": "⦄",
    "⟨": "⟩",
}
_DOSSIER_RELATION_BINDER_TOKENS = (
    "∈",
    "∉",
    "≤",
    "≥",
    "≠",
    "<=",
    ">=",
    "=",
    "<",
    ">",
    "∣",
)

# Scratch is diagnostic search memory, not proof authority. Keep it large
# enough to preserve routes across many goals while preventing recursive child
# handoffs from making every checkpoint grow without bound.
_MAX_DOSSIER_SCRATCH_RECORDS = 128
_MAX_DOSSIER_SCRATCH_RECORDS_PER_GOAL = 16
_MAX_DOSSIER_FAILED_SCRATCH_RECORDS_PER_GOAL = 8


def dossier_root_equivalence_placeholder(statement: str) -> bool:
    """Whether a root target is a synthetic placeholder, not a real theorem.

    Many infrastructure tests use `True`, `False`, or single-letter Props as
    cheap theorem stand-ins. Treating those placeholders as real root targets
    makes every ordinary `: True` helper look like a root-equivalent solution
    and incorrectly hides it from helper replay/inventory paths. Real
    PutnamBench roots are not in this placeholder set, so normal
    root-equivalent suppression remains unchanged.
    """

    return " ".join(str(statement or "").split()).strip() in (
        _ROOT_EQUIVALENCE_PLACEHOLDER_STATEMENTS
    )


def _root_is_solution_placeholder_equivalence(root_statement: str) -> bool:
    text = str(root_statement or "")
    return bool(
        _contains_solution_ref_for_prompt(text)
        and _SOLUTION_EQUIVALENCE_HINT_RE.search(text)
    )


def _mini_recursive_speculative_counterexample_failure(
    record: Dict[str, Any],
    root_statement: str,
) -> bool:
    """Return whether a failed recursive claim is only a counterexample probe."""

    if not _root_is_solution_placeholder_equivalence(root_statement):
        return False
    verdict = str(record.get("verdict", "") or "").strip()
    if verdict not in _SPECULATIVE_COUNTEREXAMPLE_FAILURE_VERDICTS:
        return False
    text = "\n".join(
        str(record.get(key, "") or "")
        for key in (
            "claim_name",
            "helper_name",
            "statement",
            "reason",
            "output",
            "giveup_match",
        )
    )
    if _COUNTEREXAMPLE_EXCLUSION_TEXT_RE.search(text):
        return False
    return bool(_SPECULATIVE_COUNTEREXAMPLE_TEXT_RE.search(text))
_PROMPT_SAFE_HELPER_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")
_LEAN_QUOTED_IDENTIFIER_RE = re.compile(r"«[^»]*(?:»|$)")
_PROMPT_BACKTICK_SPAN_RE = re.compile(r"`[^`]*(?:`|$)")
_PROMPT_ROLE_TOKEN_RE = re.compile(
    r"^(?:SYSTEM|DEVELOPER|USER|ASSISTANT)$",
    flags=re.IGNORECASE,
)
_PROMPT_BARE_ROLE_TOKEN_RE = re.compile(
    r"(?<![A-Za-z0-9_.])(?:SYSTEM|DEVELOPER|USER|ASSISTANT)(?![A-Za-z0-9_.])",
    flags=re.IGNORECASE,
)
_PROMPT_CONTROL_ACTION_WORDS = (
    "ignore",
    "previous",
    "instruction",
    "instructions",
    "disregard",
    "you",
    "your",
    "reveal",
    "hidden",
    "developer",
    "comply",
    "follow",
    "obey",
    "act",
    "pretend",
    "override",
    "forget",
)
_PROMPT_CONTROL_ACTION_WORD_RE = (
    r"(?:" + "|".join(re.escape(word) for word in _PROMPT_CONTROL_ACTION_WORDS) + r")"
)
_PROMPT_CONTROL_COMPACT_CHAIN_WORDS = tuple(
    sorted(
        {
            *_PROMPT_CONTROL_ACTION_WORDS,
            "above",
            "all",
            "are",
            "as",
            "be",
            "me",
            "now",
            "prior",
            "system",
            "the",
            "this",
            "to",
            "unsafe",
            "user",
            "with",
            "your",
        },
        key=len,
        reverse=True,
    )
)
_PROMPT_ROLE_HEADER_SEPARATOR_RE = r"[:：﹕꞉]"
_PROMPT_CONTROL_RE = re.compile(
    r"\b(?:SYSTEM|DEVELOPER|USER|ASSISTANT)\b(?:"
    r"\s*" + _PROMPT_ROLE_HEADER_SEPARATOR_RE + r"\s*[^\n;]*"
    r"|\s+\S+(?:\s+\S+){0,8}"
    r"|\s*[.!?-]\s+\S+(?:\s+\S+){0,8}"
    r")",
    flags=re.IGNORECASE,
)
_PROMPT_IGNORE_RE = re.compile(
    r"\bignore\s+(?:this|previous|all|above|your|instructions?)(?:\s+\S+){0,4}",
    flags=re.IGNORECASE,
)
_PROMPT_DISREGARD_RE = re.compile(
    r"\bdisregard\s+(?:all\s+)?(?:prior|previous|above)?\s*"
    r"instructions?(?:\s+\S+){0,4}",
    flags=re.IGNORECASE,
)
_PROMPT_STANDALONE_ACTION_RE = re.compile(
    r"\b(?:forget|reveal|override|follow|obey|comply|act|pretend)\s+"
    r"(?:all\s+|your\s+|previous\s+|prior\s+|above\s+|hidden\s+|with\s+|as\s+|to\s+|be\s+|the\s+|system\s+|developer\s+|user\s+|me\s+)*"
    r"(?:instructions?|hidden|system|developer|user|me)\b(?:\s+\S+){0,4}",
    flags=re.IGNORECASE,
)
_PROMPT_SPLIT_GAP_RE = r"(?:[^A-Za-z0-9_])*"
_PROMPT_SPLIT_WORD_SEP_RE = r"(?:[^A-Za-z0-9_])+"
_PROMPT_CONTROL_SPLIT_GAP_RE = r"(?:[^A-Za-z0-9])*"
_PROMPT_CONTROL_SPLIT_WORD_SEP_RE = r"(?:[^A-Za-z0-9])+"
_PROMPT_SPLIT_IDENTIFIER_GAP_RE = r"(?:[^A-Za-z0-9_\s])*"
_SPLIT_IDENTIFIER_PREFIX_RE = (
    r"[A-Za-z_](?:" + _PROMPT_SPLIT_IDENTIFIER_GAP_RE + r"[A-Za-z0-9_'.])*"
)
_SPLIT_SOLUTION_REF_RE = re.compile(
    r"(?<![A-Za-z0-9_.])"
    r"['`]*"
    + _SPLIT_IDENTIFIER_PREFIX_RE
    + _PROMPT_SPLIT_GAP_RE
    + r"_"
    + _PROMPT_SPLIT_GAP_RE
    + r"s"
    + _PROMPT_SPLIT_GAP_RE
    + r"o"
    + _PROMPT_SPLIT_GAP_RE
    + r"l"
    + _PROMPT_SPLIT_GAP_RE
    + r"u"
    + _PROMPT_SPLIT_GAP_RE
    + r"t"
    + _PROMPT_SPLIT_GAP_RE
    + r"i"
    + _PROMPT_SPLIT_GAP_RE
    + r"o"
    + _PROMPT_SPLIT_GAP_RE
    + r"n[A-Za-z0-9_'.]*"
    r"['`]*"
    r"(?![A-Za-z0-9_.])"
)
_SPLIT_QUOTED_SOLUTION_REF_RE = re.compile(
    r"(?<![A-Za-z0-9_.])"
    r"(?:['`][A-Za-z0-9_'.]+['`](?:\s+|[^\w\s]+)?){1,12}"
    r"(?![A-Za-z0-9_.])"
)
_NON_LEAN_DECL_APPLICATION_ERROR_RE = re.compile(
    r"(?:transport|infrastructure|exception|timeout|connection|network|http|"
    r"api|client|runtimeerror|typeerror|valueerror|keyerror|attributeerror|"
    r"oserror|pooltimeout|readtimeout|writetimeout|connecttimeout|state_sync|"
    r"answer_unsafe)",
    flags=re.IGNORECASE,
)


def _split_prompt_word_pattern(word: str) -> str:
    return (
        _PROMPT_CONTROL_SPLIT_GAP_RE
        + _PROMPT_CONTROL_SPLIT_GAP_RE.join(re.escape(ch) for ch in word)
        + _PROMPT_CONTROL_SPLIT_GAP_RE
    )


def _split_prompt_word_body_pattern(word: str) -> str:
    return _PROMPT_CONTROL_SPLIT_GAP_RE.join(re.escape(ch) for ch in word)


def _split_prompt_phrase_pattern(*words: str) -> str:
    return _PROMPT_CONTROL_SPLIT_GAP_RE.join(
        _split_prompt_word_body_pattern(word) for word in words
    )


_SPLIT_PROMPT_ROLE_WORD_RE = (
    r"(?:"
    + "|".join(
        _split_prompt_word_pattern(word)
        for word in ("SYSTEM", "DEVELOPER", "USER", "ASSISTANT")
    )
    + r")"
)
_SPLIT_PROMPT_ACTION_WORD_RE = (
    r"(?:"
    + "|".join(
        _split_prompt_word_pattern(word) for word in _PROMPT_CONTROL_ACTION_WORDS
    )
    + r")"
)
_SPLIT_PROMPT_ROLE_RE = re.compile(
    r"(?<![A-Za-z0-9])"
    + _SPLIT_PROMPT_ROLE_WORD_RE
    + r"(?![A-Za-z0-9])(?:"
    + _PROMPT_CONTROL_SPLIT_GAP_RE
    + _PROMPT_ROLE_HEADER_SEPARATOR_RE
    + _PROMPT_CONTROL_SPLIT_GAP_RE
    + r"[^\n;]*"
    + r"|"
    + _PROMPT_CONTROL_SPLIT_WORD_SEP_RE
    + _SPLIT_PROMPT_ACTION_WORD_RE
    + r"(?:\s+\S+){0,8})",
    flags=re.IGNORECASE,
)
_SPLIT_PROMPT_COMPACT_CHAIN_WORD_RE = (
    r"(?:"
    + "|".join(
        _split_prompt_word_body_pattern(word)
        for word in _PROMPT_CONTROL_COMPACT_CHAIN_WORDS
    )
    + r")"
)
_SPLIT_PROMPT_COMPACT_ROLE_ACTION_RE = re.compile(
    r"(?<![A-Za-z0-9_])"
    + _SPLIT_PROMPT_ROLE_WORD_RE
    + _SPLIT_PROMPT_COMPACT_CHAIN_WORD_RE
    + _SPLIT_PROMPT_COMPACT_CHAIN_WORD_RE
    + r"(?:" + _SPLIT_PROMPT_COMPACT_CHAIN_WORD_RE + r"){0,8}"
    + r"(?![A-Za-z0-9_])",
    flags=re.IGNORECASE,
)
_SPLIT_PROMPT_STANDALONE_ACTION_RE = re.compile(
    r"(?<![A-Za-z0-9_])"
    + r"(?:"
    + "|".join(
        _split_prompt_word_body_pattern(word)
        for word in (
            "forget",
            "reveal",
            "override",
            "follow",
            "obey",
            "comply",
            "act",
            "pretend",
        )
    )
    + r")"
    + _SPLIT_PROMPT_COMPACT_CHAIN_WORD_RE
    + r"(?:" + _SPLIT_PROMPT_COMPACT_CHAIN_WORD_RE + r"){0,8}"
    + r"(?![A-Za-z0-9_])",
    flags=re.IGNORECASE,
)
_SPLIT_PROMPT_IGNORE_RE = re.compile(
    r"(?<![A-Za-z0-9_])(?:"
    + "|".join(
        _split_prompt_phrase_pattern(*phrase)
        for phrase in (
            ("ignore", "previous", "instructions"),
            ("ignore", "instruction"),
            ("ignore", "instructions"),
            ("ignore", "this"),
            ("ignore", "your", "instructions"),
            ("ignore", "your"),
            ("ignore", "previous"),
            ("ignore", "all", "instructions"),
            ("ignore", "all"),
            ("ignore", "above", "instructions"),
            ("ignore", "above"),
        )
    )
    + r")(?![A-Za-z0-9_])",
    flags=re.IGNORECASE,
)
_SPLIT_PROMPT_DISREGARD_RE = re.compile(
    r"(?<![A-Za-z0-9_])(?:"
    + "|".join(
        _split_prompt_phrase_pattern(*phrase)
        for phrase in (
            ("disregard", "all", "prior", "instructions"),
            ("disregard", "all", "previous", "instructions"),
            ("disregard", "all", "above", "instructions"),
            ("disregard", "all", "instructions"),
            ("disregard", "prior", "instructions"),
            ("disregard", "previous", "instructions"),
            ("disregard", "above", "instructions"),
            ("disregard", "instruction"),
            ("disregard", "instructions"),
        )
    )
    + r")(?![A-Za-z0-9_])",
    flags=re.IGNORECASE,
)
_SPLIT_PROMPT_IGNORE_TARGET_RE = re.compile(
    r"(?<![A-Za-z0-9_])"
    + _split_prompt_word_body_pattern("ignore")
    + _PROMPT_CONTROL_SPLIT_WORD_SEP_RE
    + r"(?:"
    + "|".join(
        _split_prompt_word_pattern(word)
        for word in ("this", "previous", "all", "above", "instruction", "instructions")
    )
    + r")(?:"
    + _PROMPT_CONTROL_SPLIT_WORD_SEP_RE
    + _split_prompt_word_pattern("instructions")
    + r")?",
    flags=re.IGNORECASE,
)
_SPLIT_PROMPT_DISREGARD_TARGET_RE = re.compile(
    r"(?<![A-Za-z0-9_])"
    + _split_prompt_word_body_pattern("disregard")
    + _PROMPT_CONTROL_SPLIT_WORD_SEP_RE
    + r"(?:"
    + _split_prompt_word_pattern("all")
    + _PROMPT_CONTROL_SPLIT_WORD_SEP_RE
    + r")?(?:"
    + "|".join(
        _split_prompt_word_pattern(word)
        for word in ("prior", "previous", "above")
    )
    + r")?"
    + _PROMPT_CONTROL_SPLIT_GAP_RE
    + _split_prompt_word_pattern("instructions"),
    flags=re.IGNORECASE,
)

_PROMPT_CONFUSABLE_ASCII_MAP = str.maketrans({
    "Α": "A",
    "А": "A",
    "ɑ": "a",
    "α": "a",
    "а": "a",
    "Β": "B",
    "В": "B",
    "С": "C",
    "Ϲ": "C",
    "с": "c",
    "ϲ": "c",
    "Ε": "E",
    "Е": "E",
    "е": "e",
    "Η": "H",
    "Н": "H",
    "һ": "h",
    "Ι": "I",
    "І": "I",
    "і": "i",
    "Κ": "K",
    "К": "K",
    "κ": "k",
    "Μ": "M",
    "М": "M",
    "м": "m",
    "Ν": "N",
    "О": "O",
    "Ο": "O",
    "ο": "o",
    "о": "o",
    "Ρ": "P",
    "Р": "P",
    "р": "p",
    "Ѕ": "S",
    "Տ": "S",
    "ѕ": "s",
    "Τ": "T",
    "Т": "T",
    "τ": "t",
    "т": "t",
    "Υ": "Y",
    "У": "Y",
    "υ": "y",
    "у": "y",
    "Χ": "X",
    "Х": "X",
    "х": "x",
})


def _prompt_security_fold_text(text: str) -> str:
    """Fold fullwidth ASCII controls without normalizing Lean math symbols."""

    out: List[str] = []
    for ch in str(text or ""):
        code = ord(ch)
        if 0xFF01 <= code <= 0xFF5E:
            out.append(chr(code - 0xFEE0))
        elif code == 0x3000:
            out.append(" ")
        else:
            out.append(ch)
    return "".join(out)


def _prompt_security_skeleton_with_index_map(text: str) -> Tuple[str, List[int]]:
    """Return a detection-only Latin skeleton plus original-char indexes."""

    skeleton: List[str] = []
    index_map: List[int] = []
    for index, ch in enumerate(str(text or "")):
        normalized = unicodedata.normalize("NFKC", ch)
        if not normalized:
            continue
        for item in normalized:
            skeleton.append(item.translate(_PROMPT_CONFUSABLE_ASCII_MAP))
            index_map.append(index)
    return "".join(skeleton), index_map


def _prompt_security_skeleton_text(text: str) -> str:
    skeleton, _index_map = _prompt_security_skeleton_with_index_map(text)
    return skeleton


def _redact_security_skeleton_matches(
    text: str,
    patterns: Sequence[re.Pattern[str]],
    *,
    label: str,
    predicate: Optional[Any] = None,
) -> str:
    """Redact original spans whose security skeleton matches a hazard."""

    raw = str(text or "")
    if not raw:
        return raw
    skeleton, index_map = _prompt_security_skeleton_with_index_map(raw)
    if not skeleton or not index_map:
        return raw
    spans: List[Tuple[int, int]] = []
    for pattern in patterns:
        for match in pattern.finditer(skeleton):
            if predicate is not None and not bool(predicate(match)):
                continue
            if match.start() >= len(index_map) or match.end() <= 0:
                continue
            start = index_map[match.start()]
            end = index_map[min(match.end() - 1, len(index_map) - 1)] + 1
            if start < end:
                spans.append((start, end))
    if not spans:
        return raw
    spans.sort()
    merged: List[Tuple[int, int]] = []
    for start, end in spans:
        if not merged or start > merged[-1][1]:
            merged.append((start, end))
        else:
            prev_start, prev_end = merged[-1]
            merged[-1] = (prev_start, max(prev_end, end))
    out: List[str] = []
    last = 0
    for start, end in merged:
        out.append(raw[last:start])
        out.append(f"{label}_{_prompt_redaction_hash(raw[start:end])}")
        last = end
    out.append(raw[last:])
    return "".join(out)


def helper_decl_name(src: str) -> Optional[str]:
    """Return the declared name of a helper block, if it has one."""
    return graph_helper_decl_name(src) or None


def official_answer_visible_to_llm(
    *,
    opaque_mode: bool,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
) -> bool:
    """Return the single capability boundary for official-answer visibility.

    Authorization is deliberately strict: a non-opaque request and an allow
    flag are insufficient unless the adapter also positively attests that the
    official-answer payload is present.  Keeping this predicate here prevents
    prompt, graph, recursive-child, and proof-state code from independently
    interpreting the three inputs.
    """

    return bool(
        not opaque_mode
        and allow_official_answer_visibility
        and official_answer_payload_present is True
    )


def effective_solution_placeholder_suppression(
    *,
    suppress_solution_placeholders: Optional[bool] = True,
    opaque_mode: bool = True,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
) -> bool:
    """Whether placeholder redaction is active under the effective capability.

    ``None`` retains the historical auto-detect meaning and therefore remains
    enabled for text that actually contains a benchmark solution reference.
    Callers that already know the project is generic pass ``False``.
    """

    official_answer_visible = official_answer_visible_to_llm(
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
        official_answer_payload_present=official_answer_payload_present,
    )
    if not opaque_mode and allow_official_answer_visibility:
        # A visible-answer capability request is fail-closed: if its payload
        # attestation is missing or false after checkpoint restore, solution
        # symbols must become hidden again even when the serialized convenience
        # flag still says ``False``.
        return not official_answer_visible
    if official_answer_payload_present is True:
        # A positive payload attestation means these are official-answer
        # symbols, not generic project declarations that merely happen to end
        # in ``_solution``.  The visibility capability is authoritative even
        # when a stale checkpoint or legacy caller supplies a contradictory
        # ``suppress_solution_placeholders=False`` flag.
        return not official_answer_visible
    return bool(
        suppress_solution_placeholders is not False
        and not official_answer_visible
    )


def is_answer_unsafe_helper_source(
    src: str,
    *,
    suppress_solution_placeholders: Optional[bool] = None,
    opaque_mode: bool = True,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
) -> bool:
    """Whether a helper block attempts to materialize a ``*_solution`` name."""

    if not effective_solution_placeholder_suppression(
        suppress_solution_placeholders=suppress_solution_placeholders,
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
        official_answer_payload_present=official_answer_payload_present,
    ):
        return False
    if suppress_solution_placeholders is None and not _PUTNAM_SOLUTION_REF_RE.search(
        _prompt_security_skeleton_text(src)
    ):
        return False
    text = str(src or "")
    name = helper_decl_name(text) or ""
    if _contains_solution_ref_for_prompt(name):
        return True
    if _MATERIALIZED_SOLUTION_DECL_RE.search(text):
        return True
    statement = helper_decl_statement(text)
    if statement and _contains_solution_ref_for_prompt(statement):
        return True
    if not statement and _contains_solution_ref_for_prompt(text):
        return True
    body = helper_decl_body(text)
    return bool(body and _contains_solution_ref_for_prompt(body))


def is_answer_unsafe_statement_text(
    text: str,
    *,
    suppress_solution_placeholders: Optional[bool] = None,
    opaque_mode: bool = True,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
) -> bool:
    """Whether a goal/helper statement refers to a hidden answer placeholder."""

    if not effective_solution_placeholder_suppression(
        suppress_solution_placeholders=suppress_solution_placeholders,
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
        official_answer_payload_present=official_answer_payload_present,
    ):
        return False
    if suppress_solution_placeholders is None and not _PUTNAM_SOLUTION_REF_RE.search(
        _prompt_security_skeleton_text(text)
    ):
        return False
    return _contains_solution_ref_for_prompt(text)


def _strip_lean_comments_for_prompt(text: str) -> str:
    """Remove Lean comments before echoing untrusted snippets to the model."""

    source = str(text or "")
    out: List[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        ch = source[index]
        nxt = source[index + 1] if index + 1 < len(source) else ""
        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                index += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth = max(0, block_depth - 1)
                index += 2
                continue
            if ch in "\r\n":
                out.append("\n")
            index += 1
            continue
        if in_string:
            out.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            index += 1
            continue
        if ch == '"':
            in_string = True
            out.append(ch)
            index += 1
            continue
        if ch == "«":
            end = source.find("»", index + 1)
            if end < 0:
                out.append(source[index:])
                break
            out.append(source[index : end + 1])
            index = end + 1
            continue
        if ch == "-" and nxt == "-":
            index += 2
            while index < len(source) and source[index] not in "\r\n":
                index += 1
            if index < len(source):
                out.append("\n")
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            index += 2
            continue
        out.append(ch)
        index += 1
    return "".join(out)


_JSON_SAFE_KEY_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]{0,63}$")
_LEGACY_PLACEHOLDER_JSON_START_RE = re.compile(
    r'[\[{]\s*"<string>"\s*(?::|,|\]|\})',
    re.IGNORECASE,
)


def strip_legacy_placeholder_corruption_for_prompt(text: str) -> str:
    """Omit JSON payloads destroyed by the former Lean-string sanitizer.

    Older checkpoints can legitimately be resumed after this repair. Their
    persisted planner-deliberation observations may already consist of JSON
    punctuation and repeated ``"<string>"`` sentinels. Such text has no
    recoverable mathematical content and actively induces placeholder tool
    calls when replayed to a model. Preserve any meaningful prefix and mark
    only the corrupt suffix as unavailable.
    """

    source = str(text or "")
    if source.lower().count("<string>") < 3:
        return source
    match = _LEGACY_PLACEHOLDER_JSON_START_RE.search(source)
    if match is None:
        return source
    suffix = source[match.start() :]
    if suffix.lower().count("<string>") < 3:
        return source
    prefix = source[: match.start()].rstrip()
    marker = "[legacy corrupted deliberation payload omitted]"
    return f"{prefix}\n{marker}" if prefix else marker


def redact_json_string_values_for_prompt(text: str) -> str:
    """Redact JSON string VALUES while preserving structure and object keys.

    ``_redact_string_literals_for_prompt`` exists for Lean source, where any
    double-quoted literal may carry the answer.  Applying it to a JSON tool-call
    payload replaces the keys too, so a malformed call renders as
    ``{"<string>": ["<string>"`` and nobody — model or operator — can tell what
    was wrong.  The same disease already made provider 400 bodies undiagnosable
    (see ``format_exception``).

    Argument keys come from our own tool schemas, so preserving them is safe and
    is what makes the diagnostic actionable: the shape alone distinguishes a
    truncated payload from a wrong-shaped one.  A key is kept only when it looks
    like a plain identifier and survives answer-reference redaction; everything
    else, including every value, is replaced.
    """

    source = str(text or "")
    out: List[str] = []
    index = 0
    length = len(source)
    while index < length:
        ch = source[index]
        if ch != '"':
            out.append(ch)
            index += 1
            continue
        # Consume the string literal, tracking escapes.
        cursor = index + 1
        literal: List[str] = []
        closed = False
        while cursor < length:
            current = source[cursor]
            if current == "\\" and cursor + 1 < length:
                literal.append(source[cursor : cursor + 2])
                cursor += 2
                continue
            if current == '"':
                closed = True
                break
            literal.append(current)
            cursor += 1
        body = "".join(literal)
        # A key is a literal whose next non-space character is ``:``.
        lookahead = cursor + 1
        while lookahead < length and source[lookahead] in " \t\r\n":
            lookahead += 1
        is_key = closed and lookahead < length and source[lookahead] == ":"
        if is_key and _JSON_SAFE_KEY_RE.fullmatch(body):
            safe_key = _redact_solution_refs_for_prompt(body)
            out.append(f'"{safe_key}"' if safe_key == body else '"<string>"')
        else:
            out.append('"<string>"')
        index = cursor + 1 if closed else length
        if not closed:
            break
    return "".join(out)


def _prompt_safe_composed_prompt_block(text: str) -> str:
    """Re-check a block assembled from individually-sanitized fragments.

    Joining sanitized items with punctuation ("\\n- ", ": ", ". ") is not
    closed under the answer/control rules: a reference split across the join
    matches nothing in either fragment while the composed block spells it out.
    Only the split-aware rules are re-applied, so identifiers a caller has
    already vetted for display survive.
    """

    composed = str(text or "")
    composed = _redact_solution_refs_for_prompt(composed)
    composed = _redact_split_solution_refs_for_prompt(composed)
    composed = _redact_split_prompt_control_text(composed)
    return composed


def prompt_safe_malformed_tool_arguments(text: str, *, limit: int = 1600) -> str:
    """Render an unparseable tool-call payload so it stays diagnosable.

    Deliberately NOT ``_prompt_safe_inline_text``: that redacts every quoted
    literal, including the schema keys, which is what reduced these previews to
    ``{"<string>": ["<string>"`` and made truncated payloads indistinguishable
    from wrong-shaped ones.  Values are still fully replaced, keys survive only
    as vetted plain identifiers, and the whole result is swept for answer
    references, so nothing quoted by the model reaches the prompt verbatim.
    """

    redacted = redact_json_string_values_for_prompt(text)
    redacted = _redact_solution_refs_for_prompt(redacted)
    redacted = _redact_split_solution_refs_for_prompt(redacted)
    # A malformed payload need not be JSON at all — it can be bare prose, which
    # has no quoted spans for the pass above to touch. Prompt-control phrases
    # must still be hidden there, or relaxing the literal redaction would open
    # an injection path for exactly the non-JSON case.
    redacted = _redact_prompt_control_text(redacted)
    redacted = _redact_split_prompt_control_text(redacted)
    collapsed = " ".join(str(redacted or "").split())
    cap = max(40, int(limit or 1600))
    if len(collapsed) > cap:
        collapsed = collapsed[: max(0, cap - 3)].rstrip() + "..."
    return collapsed


def _redact_string_literals_for_prompt(text: str) -> str:
    """Replace Lean string literal contents before prompt rendering."""

    source = str(text or "")
    out: List[str] = []
    index = 0
    in_string = False
    escaped = False
    emitted_placeholder = False
    while index < len(source):
        ch = source[index]
        if in_string:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                out.append('"')
                in_string = False
                emitted_placeholder = False
            index += 1
            continue
        if ch == '"':
            out.append('"')
            out.append("<string>")
            in_string = True
            emitted_placeholder = True
            index += 1
            continue
        out.append(ch)
        index += 1
    if in_string and emitted_placeholder:
        out.append('"')
    return "".join(out)


def _prompt_safe_helper_name(
    name: str,
    *,
    redact_solution_refs: bool = True,
) -> str:
    """Return a prompt-safe display token for a helper name."""

    raw = " ".join(_strip_lean_comments_for_prompt(name).split()).strip()
    skeleton = _prompt_security_skeleton_text(raw)
    if (
        _PROMPT_SAFE_HELPER_NAME_RE.fullmatch(raw)
        and (not redact_solution_refs or not _contains_solution_ref_for_prompt(raw))
        and not _PROMPT_ROLE_TOKEN_RE.fullmatch(skeleton)
        and not _PROMPT_CONTROL_RE.search(skeleton)
        and not _PROMPT_IGNORE_RE.search(skeleton)
        and not _PROMPT_STANDALONE_ACTION_RE.search(skeleton)
        and not _SPLIT_PROMPT_COMPACT_ROLE_ACTION_RE.search(skeleton)
        and not _SPLIT_PROMPT_STANDALONE_ACTION_RE.search(skeleton)
        and not _SPLIT_PROMPT_IGNORE_RE.search(skeleton)
        and not _SPLIT_PROMPT_DISREGARD_RE.search(skeleton)
    ):
        return raw
    return f"helper_name_hidden_{text_hash(raw)}"


def _redact_quoted_identifiers_for_prompt(
    text: str,
    *,
    preserve_solution_refs: bool = False,
    preserve_safe_lean_identifiers: bool = False,
) -> str:
    """Hide Lean quoted identifier contents before prompt rendering."""

    def repl(match: re.Match[str]) -> str:
        raw = match.group(0)
        if preserve_solution_refs and _contains_solution_ref_for_prompt(raw):
            return raw
        if preserve_safe_lean_identifiers:
            inner = raw[1:-1] if raw.startswith("«") and raw.endswith("»") else raw
            if inner and _lean_diagnostic_identifier_text_is_safe(inner):
                return raw
        return f"«identifier_hidden_{text_hash(raw)}»"

    return _LEAN_QUOTED_IDENTIFIER_RE.sub(repl, str(text or ""))


def _redact_backtick_spans_for_prompt(
    text: str,
    *,
    preserve_solution_refs: bool = False,
    keep_contents: bool = False,
) -> str:
    """Hide markdown/Lean code span contents in untrusted prompt text."""

    def repl(match: re.Match[str]) -> str:
        if preserve_solution_refs and _contains_solution_ref_for_prompt(match.group(0)):
            return match.group(0)
        if keep_contents:
            inner = str(match.group(0))[1:-1]
            return f"'{inner}'"
        return f"`code_hidden_{text_hash(match.group(0))}`"

    return _PROMPT_BACKTICK_SPAN_RE.sub(repl, str(text or ""))


def _preserve_backtick_spans_for_lean_diagnostic(
    text: str,
    *,
    preserve_solution_refs: bool = False,
) -> str:
    """Render Lean diagnostic code spans without letting spans contaminate neighbors."""

    raw = str(text or "")
    if len(raw) < 2 or not raw.startswith("`") or not raw.endswith("`"):
        return f"`code_hidden_{text_hash(raw)}`"
    inner = raw[1:-1]
    if not preserve_solution_refs:
        inner = _redact_solution_refs_for_prompt(inner)
    inner = _redact_prompt_control_text(inner)
    return f"'{inner}'"


def _prompt_redaction_hash(text: str) -> str:
    return hashlib.sha256(str(text or "").encode("utf-8", errors="replace")).hexdigest()[:16]


def _redact_prompt_control_text(text: str) -> str:
    """Hide plain prompt-control phrases in untrusted prompt text."""

    safe = str(text or "")
    return _redact_security_skeleton_matches(
        safe,
        (
            _PROMPT_CONTROL_RE,
            _PROMPT_BARE_ROLE_TOKEN_RE,
            _PROMPT_IGNORE_RE,
            _PROMPT_DISREGARD_RE,
            _PROMPT_STANDALONE_ACTION_RE,
        ),
        label="prompt_control_hidden",
    )


def _redact_split_prompt_control_text(text: str) -> str:
    """Hide prompt-control phrases split across preserved Lean code spans."""

    safe = str(text or "")
    return _redact_security_skeleton_matches(
        safe,
        (
            _SPLIT_PROMPT_IGNORE_RE,
            _SPLIT_PROMPT_DISREGARD_RE,
            _SPLIT_PROMPT_ROLE_RE,
            _SPLIT_PROMPT_COMPACT_ROLE_ACTION_RE,
            _SPLIT_PROMPT_STANDALONE_ACTION_RE,
            _SPLIT_PROMPT_IGNORE_TARGET_RE,
            _SPLIT_PROMPT_DISREGARD_TARGET_RE,
        ),
        label="prompt_control_hidden",
    )


def _redact_solution_refs_for_prompt(text: str) -> str:
    """Hide answer-placeholder identifiers in untrusted prompt text."""

    return _redact_security_skeleton_matches(
        text,
        (_SOLUTION_REF_RE,),
        label="solution_ref_hidden",
    )


def _redact_split_solution_refs_for_prompt(text: str) -> str:
    """Hide answer refs split across preserved diagnostic code spans."""

    def quoted_predicate(match: re.Match[str]) -> bool:
        normalized = re.sub(r"[^A-Za-z0-9_]+", "", match.group(0))
        return bool(_SOLUTION_REF_RE.search(normalized))

    safe = _redact_security_skeleton_matches(
        text,
        (_SPLIT_QUOTED_SOLUTION_REF_RE,),
        label="solution_ref_hidden",
        predicate=quoted_predicate,
    )
    return _redact_security_skeleton_matches(
        safe,
        (_SPLIT_SOLUTION_REF_RE,),
        label="solution_ref_hidden",
    )


def _strip_lean_comments_outside_backtick_spans_for_prompt(text: str) -> str:
    """Strip comments in prose while preserving Lean diagnostic code atoms."""

    raw = str(text or "")
    out: List[str] = []
    index = 0
    while index < len(raw):
        if raw.startswith("--", index):
            newline = raw.find("\n", index)
            if newline < 0:
                break
            out.append("\n")
            index = newline + 1
            continue
        if raw.startswith("/-", index):
            depth = 1
            index += 2
            while index < len(raw) and depth > 0:
                if raw.startswith("/-", index):
                    depth += 1
                    index += 2
                elif raw.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            out.append(" ")
            continue
        ch = raw[index]
        if ch == '"':
            out.append(ch)
            index += 1
            escaped = False
            while index < len(raw):
                out.append(raw[index])
                if escaped:
                    escaped = False
                elif raw[index] == "\\":
                    escaped = True
                elif raw[index] == '"':
                    index += 1
                    break
                index += 1
            continue
        if ch == "`":
            end = raw.find("`", index + 1)
            if end >= 0:
                out.append(raw[index : end + 1])
                index = end + 1
                continue
        out.append(ch)
        index += 1
    return "".join(out)


def _contains_solution_ref_for_prompt(text: str) -> bool:
    """Return whether prompt text contains a direct or split answer ref."""

    raw = _prompt_security_skeleton_text(text)
    if _SOLUTION_REF_RE.search(raw) or _SPLIT_SOLUTION_REF_RE.search(raw):
        return True
    for match in _SPLIT_QUOTED_SOLUTION_REF_RE.finditer(raw):
        normalized = re.sub(r"[^A-Za-z0-9_]+", "", match.group(0))
        if _SOLUTION_REF_RE.search(normalized):
            return True
    return False


def _lean_diagnostic_identifier_text_is_safe(text: str) -> bool:
    """Whether a Lean quoted identifier can remain visible in diagnostics."""

    raw = str(text or "")
    if not raw:
        return False
    if _contains_solution_ref_for_prompt(raw):
        return False
    skeleton = _prompt_security_skeleton_text(raw)
    if (
        _PROMPT_CONTROL_RE.search(skeleton)
        or _PROMPT_BARE_ROLE_TOKEN_RE.search(skeleton)
        or _PROMPT_IGNORE_RE.search(skeleton)
        or _PROMPT_DISREGARD_RE.search(skeleton)
    ):
        return False
    return _redact_split_prompt_control_text(raw) == raw


def _decl_application_error_is_lean_diagnostic(
    error_kind: str,
    error_text: str,
) -> bool:
    """Whether an apply-declaration error is Lean feedback, not infra prose."""

    if not str(error_text or "").strip():
        return False
    return not bool(_NON_LEAN_DECL_APPLICATION_ERROR_RE.search(str(error_kind or "")))


def _collapse_prompt_whitespace(
    text: str,
    *,
    preserve_quoted_identifier_whitespace: bool = False,
) -> str:
    """Collapse layout whitespace without mutating Lean quoted identifiers."""

    if not preserve_quoted_identifier_whitespace:
        return " ".join(str(text or "").split())
    source = str(text or "")
    out: List[str] = []
    index = 0
    pending_space = False
    while index < len(source):
        ch = source[index]
        if ch == "«":
            if pending_space and out:
                out.append(" ")
            pending_space = False
            end = source.find("»", index + 1)
            if end < 0:
                out.append(source[index:])
                break
            out.append(source[index : end + 1])
            index = end + 1
            continue
        if ch.isspace():
            pending_space = True
            index += 1
            continue
        if pending_space and out:
            out.append(" ")
        pending_space = False
        out.append(ch)
        index += 1
    return "".join(out).strip()


def _normalize_prompt_layout(text: str) -> str:
    """Preserve Lean layout while dropping irrelevant trailing whitespace."""

    lines = str(text or "").strip().splitlines()
    return "\n".join(line.rstrip() for line in lines)


def _prompt_safe_inline_text(
    text: str,
    *,
    limit: int,
    redact_solution_refs: bool = True,
    preserve_backtick_contents: bool = False,
    preserve_safe_lean_identifiers: bool = False,
    preserve_quoted_identifier_whitespace: bool = False,
    preserve_layout: bool = False,
    truncate: bool = True,
) -> str:
    """Compact untrusted state for a single prompt line.

    ``truncate=False`` preserves a complete sanitized unit for callers that
    perform structural whole-unit packing after sanitization. This prevents a
    redaction expansion (notably escaped Lean identifiers) from reintroducing
    a mid-declaration cut before the structural budgeter sees the result.
    """

    safe = _strip_lean_comments_for_prompt(text)
    safe = _redact_string_literals_for_prompt(safe)
    if redact_solution_refs:
        safe = _redact_split_solution_refs_for_prompt(safe)
    safe = _redact_quoted_identifiers_for_prompt(
        safe,
        preserve_solution_refs=not redact_solution_refs,
        preserve_safe_lean_identifiers=preserve_safe_lean_identifiers,
    )
    safe = _redact_backtick_spans_for_prompt(
        safe,
        preserve_solution_refs=not redact_solution_refs,
        keep_contents=preserve_backtick_contents,
    )
    safe = _redact_prompt_control_text(safe)
    safe = _redact_split_prompt_control_text(safe)
    if redact_solution_refs:
        safe = _redact_solution_refs_for_prompt(safe)
        safe = _redact_split_solution_refs_for_prompt(safe)
    safe = safe.replace("`", "'")
    if preserve_layout:
        safe = _normalize_prompt_layout(safe)
    else:
        safe = _collapse_prompt_whitespace(
            safe,
            preserve_quoted_identifier_whitespace=(
                preserve_quoted_identifier_whitespace
            ),
        )
    if truncate and len(safe) > limit:
        safe = safe[: max(0, limit - 3)].rstrip() + "..."
    return safe


def _prompt_safe_natural_language_text(
    text: Any,
    *,
    limit: int,
    redact_solution_refs: bool = True,
    preserve_layout: bool = False,
    truncate: bool = True,
) -> str:
    """Sanitize prose/search text without destroying quoted phrase content.

    Lean source must hide string-literal contents, but applying that rule to a
    mathematical explanation or theorem-search query manufactures synthetic
    ``"<string>"`` terms and makes truthful telemetry impossible. This keeps
    the prompt-control and answer-reference boundaries while preserving the
    semantic content of natural language.
    """

    safe = str(text or "").strip()
    if redact_solution_refs:
        safe = _redact_split_solution_refs_for_prompt(safe)
        safe = _redact_solution_refs_for_prompt(safe)
    safe = _redact_prompt_control_text(safe)
    safe = _redact_split_prompt_control_text(safe)
    if redact_solution_refs:
        safe = _redact_split_solution_refs_for_prompt(safe)
    safe = safe.replace("`", "'")
    safe = (
        _normalize_prompt_layout(safe)
        if preserve_layout
        else " ".join(safe.split())
    ).strip()
    if truncate and len(safe) > limit:
        safe = safe[: max(0, limit - 3)].rstrip() + "..."
    return safe


def _prompt_safe_lean_diagnostic_text(
    text: str,
    *,
    limit: int,
    redact_solution_refs: bool = True,
    preserve_line_breaks: bool = False,
    strip_comments: bool = True,
) -> str:
    """Compact Lean feedback while preserving diagnostic code atoms.

    Lean reports the exact failed tactic, identifier, lemma, or goal fragment in
    backtick spans. Those spans are evidence for repair, not prompt syntax.
    Keep their contents visible while still redacting strings, answer refs, and
    prompt-control phrases before the text reaches a model.
    """

    safe = (
        _strip_lean_comments_outside_backtick_spans_for_prompt(text)
        if strip_comments
        else str(text or "")
    )
    safe = _redact_string_literals_for_prompt(safe)
    if redact_solution_refs:
        safe = _redact_split_solution_refs_for_prompt(safe)

    parts: list[str] = []
    last_index = 0

    def sanitize_surrounding_text(chunk: str) -> str:
        surrounding = _redact_quoted_identifiers_for_prompt(
            chunk,
            preserve_solution_refs=not redact_solution_refs,
            preserve_safe_lean_identifiers=True,
        )
        surrounding = _redact_prompt_control_text(surrounding)
        if redact_solution_refs:
            surrounding = _redact_solution_refs_for_prompt(surrounding)
        return surrounding

    for match in _PROMPT_BACKTICK_SPAN_RE.finditer(safe):
        if match.start() > last_index:
            parts.append(sanitize_surrounding_text(safe[last_index : match.start()]))
        parts.append(
            _preserve_backtick_spans_for_lean_diagnostic(
                match.group(0),
                preserve_solution_refs=not redact_solution_refs,
            )
        )
        last_index = match.end()

    if last_index < len(safe):
        parts.append(sanitize_surrounding_text(safe[last_index:]))
    safe = "".join(parts)
    safe = _redact_split_prompt_control_text(safe)
    if redact_solution_refs:
        safe = _redact_split_solution_refs_for_prompt(safe)
    safe = safe.replace("`", "'").strip()
    if preserve_line_breaks:
        safe = "\n".join(line.rstrip() for line in safe.splitlines()).strip()
    else:
        safe = " ".join(safe.split())
    if len(safe) > limit:
        suffix = "\n... (Lean output truncated)" if preserve_line_breaks else "..."
        safe = safe[: max(0, limit - len(suffix))].rstrip() + suffix
    return safe


def _prompt_safe_code_snippet(
    text: str,
    *,
    limit: int = 800,
    redact_solution_refs: bool = True,
) -> List[str]:
    """Return bounded, comment-stripped code lines for prompt rendering."""

    safe = _strip_lean_comments_for_prompt(text)
    safe = _redact_string_literals_for_prompt(safe)
    if redact_solution_refs:
        safe = _redact_split_solution_refs_for_prompt(safe)
    safe = _redact_quoted_identifiers_for_prompt(
        safe,
        preserve_solution_refs=not redact_solution_refs,
    )
    safe = _redact_backtick_spans_for_prompt(
        safe,
        preserve_solution_refs=not redact_solution_refs,
    )
    safe = _redact_prompt_control_text(safe)
    safe = _redact_split_prompt_control_text(safe)
    if redact_solution_refs:
        safe = _redact_solution_refs_for_prompt(safe)
        safe = _redact_split_solution_refs_for_prompt(safe)
    safe = safe.replace("`", "'").strip()
    if not safe:
        return []
    if len(safe) > limit:
        safe = safe[: max(0, limit - 3)].rstrip() + "..."
    lines = [" ".join(line.rstrip().split()) for line in safe.splitlines()]
    return [line for line in lines if line][:10]


def helper_prompt_signature(
    src: str,
    *,
    name: str = "",
    redact_solution_refs: bool = True,
) -> str:
    """Render a helper declaration for prompts without exposing its body."""

    source = str(src or "").strip()
    helper_name = str(name or "").strip() or (helper_decl_name(source) or "")
    if helper_name:
        helper_name = _prompt_safe_helper_name(
            helper_name,
            redact_solution_refs=redact_solution_refs,
        )
    statement = _prompt_safe_inline_text(
        helper_decl_statement(source),
        limit=800,
        redact_solution_refs=False,
        truncate=False,
    )
    if helper_name and statement:
        return f"theorem {helper_name} : {statement} := by"
    if helper_name:
        return f"{helper_name} : <statement unavailable>"
    first = source.splitlines()[0].strip() if source else ""
    return first


def text_hash(text: str) -> str:
    return hashlib.sha256(str(text or "").encode("utf-8")).hexdigest()[:16]


_SELECTED_WORK_WRAPPER_KEYS = (
    "graph_record",
    "metadata",
    "selected_work",
    "selected_work_item",
)


def selected_work_mapping_layers(record: Any) -> List[Mapping[str, Any]]:
    """Return every known selected-work wrapper layer exactly once."""

    if not isinstance(record, Mapping):
        return []
    pending: List[Mapping[str, Any]] = [record]
    layers: List[Mapping[str, Any]] = []
    seen: Set[int] = set()
    while pending:
        layer = pending.pop(0)
        if id(layer) in seen:
            continue
        seen.add(id(layer))
        layers.append(layer)
        for key in _SELECTED_WORK_WRAPPER_KEYS:
            child = layer.get(key)
            if isinstance(child, Mapping):
                pending.append(child)
    return layers


def selected_work_has_explicit_cognition(record: Any) -> bool:
    """Match the resolver's wrapper traversal for fail-closed callers."""

    for layer in selected_work_mapping_layers(record):
        if any(
            layer.get(key)
            for key in (
                "consumer_bindings",
                "primary_cognition_scope",
                "primary_consumer_binding",
                "primary_consumer_binding_id",
                "proof_idea_id",
            )
        ):
            return True
        lineage = layer.get("proof_lineage")
        if isinstance(lineage, Mapping) and str(
            lineage.get("proof_idea_id") or ""
        ).strip():
            return True
    return False


def canonical_dossier_statement_key(statement: str) -> str:
    """Canonical key for durable dossier-level statement memories."""

    return graph_statement_key(statement)


def _mini_recursive_claim_obligation_key(
    *,
    pass_index: Any = None,
    selected_index: Any = None,
    name: str = "",
    statement: str = "",
) -> str:
    """Stable identity for one selected mini-recursive root obligation."""

    selected_text = str(selected_index or "").strip() or "unknown"
    name_text = str(name or "").strip() or "claim"
    statement_text = str(statement or "").strip()
    statement_key = canonical_dossier_statement_key(statement_text)
    statement_identity = statement_key or text_hash(statement_text)
    return "\n".join(
        str(item)
        for item in (
            "mini_recursive_contract_claim",
            f"pass={pass_index if pass_index is not None else 'unknown'}",
            f"selected={selected_text}",
            f"name={name_text}",
            f"statement={statement_identity}",
        )
        if str(item)
    )


def _mini_recursive_route_contract_identity(
    *,
    pass_index: Any = None,
    contract_claims: Sequence[Dict[str, Any]] = (),
) -> str:
    """Stable identity for one mini-recursive root-route contract instance."""

    claim_lines: List[str] = []
    for item in list(contract_claims or ()):
        if not isinstance(item, dict):
            continue
        deps = sorted(
            {
                str(dep or "").strip()
                for dep in list(item.get("dependencies") or [])
                if str(dep or "").strip()
            }
        )
        claim_lines.append(
            "|".join(
                str(part)
                for part in (
                    str(item.get("selected_index") or "").strip(),
                    str(item.get("source_index") or "").strip(),
                    str(item.get("name") or "").strip(),
                    str(item.get("statement_key") or "").strip()
                    or _mini_recursive_contract_statement_key(
                        str(item.get("statement") or "")
                    ),
                    ",".join(deps),
                )
            )
        )
    return "\n".join(
        (
            "mini_recursive_route_contract",
            f"pass={pass_index if pass_index is not None else 'unknown'}",
            *claim_lines,
        )
    )


def _mini_recursive_contract_statement_key(statement: str) -> str:
    """Stable identity for one mini-recursive contract statement."""

    statement_text = str(statement or "").strip()
    if not statement_text:
        return ""
    return canonical_dossier_statement_key(statement_text) or text_hash(statement_text)


def _bound_mini_recursive_event_contract_identity(
    record: Mapping[str, Any],
    *,
    prefix: str = "",
    statement: str = "",
) -> str:
    """Return receipt-bound Lean identity carried by recursive telemetry."""

    identity = str(record.get(f"{prefix}contract_identity") or "").strip()
    statement_key = str(
        record.get(f"{prefix}contract_identity_statement_key") or ""
    ).strip()
    environment_hash = str(
        record.get(f"{prefix}contract_identity_environment_hash") or ""
    ).strip()
    receipt = str(
        record.get(f"{prefix}contract_identity_evidence_receipt") or ""
    ).strip()
    source_statement = str(statement or "").strip()
    if (
        not has_lean_contract_identity(identity)
        or not statement_key
        or (
            source_statement
            and statement_key
            != _mini_recursive_contract_statement_key(source_statement)
        )
        or not lean_contract_evidence_receipt_matches(
            receipt,
            identity=identity,
            statement_key=statement_key,
            environment_hash=environment_hash,
        )
    ):
        return ""
    return identity


def _mini_recursive_event_contract_evidence_present(
    record: Mapping[str, Any],
    *,
    prefix: str = "",
) -> bool:
    return any(
        str(record.get(f"{prefix}{field}") or "").strip()
        for field in (
            "contract_identity",
            "contract_identity_statement_key",
            "contract_identity_environment_hash",
            "contract_identity_evidence_receipt",
        )
    )


def _mini_recursive_event_route_relation_is_valid(
    record: Mapping[str, Any],
    *,
    root_contract_identity: str,
    root_environment_hash: str,
    statement: str,
    allowed_anchor_identities: Sequence[str] = (),
) -> bool:
    """Validate a claim-to-root relation emitted by Lean adjudication."""

    claim_identity = _bound_mini_recursive_event_contract_identity(
        record,
        statement=statement,
    )
    relation_kind = str(
        record.get("contract_route_relation_kind") or ""
    ).strip().lower()
    anchor_identity = str(
        record.get("contract_route_relation_anchor_identity") or ""
    ).strip()
    relation_receipt = str(
        record.get("contract_route_relation_evidence_receipt") or ""
    ).strip()
    claim_environment_hash = str(
        record.get("contract_identity_environment_hash") or ""
    ).strip()
    claim_evidence_receipt = str(
        record.get("contract_identity_evidence_receipt") or ""
    ).strip()
    if (
        not claim_identity
        or not root_contract_identity
        or relation_kind not in {"exact", "profile"}
        or anchor_identity
        not in {
            root_contract_identity,
            *(str(item or "").strip() for item in allowed_anchor_identities),
        }
        or claim_environment_hash != str(root_environment_hash or "").strip()
        or not claim_evidence_receipt
    ):
        return False
    expected_receipt = "lean-contract-route-relation-v1:" + text_hash(
        json.dumps(
            {
                "anchor_identity": anchor_identity,
                "claim_evidence_receipt": claim_evidence_receipt,
                "environment_hash": claim_environment_hash,
                "kind": relation_kind,
            },
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        )
    )
    return bool(
        relation_receipt
        and secrets.compare_digest(relation_receipt, expected_receipt)
    )


def _mini_recursive_record_allows_contract_statement_retarget(
    record: Dict[str, Any],
) -> bool:
    """Return whether a recursive event is explicitly a statement repair.

    Aggregate root-route contracts are consumed by later scheduler turns, so a
    same pass/index event must not silently change the logical obligation unless
    it came from the mini-recursive statement-repair path.
    """

    phase = str(record.get("phase") or "").strip()
    mode = str(record.get("variant_mode") or record.get("mode") or "").strip()
    if phase in {
        "mini_recursive_claim_statement_repair",
        "mini_recursive_claim_reuse",
    }:
        return True
    if "statement_repair" in mode:
        return True
    return bool(
        str(record.get("original_statement") or "").strip()
        and str(
            record.get("repaired_statement") or record.get("statement") or ""
        ).strip()
    )


def _active_root_statement_from_hypotheses(
    target: str,
    hypotheses: Sequence[str],
) -> str:
    body = str(target or "").strip()
    pending_binders: List[str] = []

    def flush_binders() -> None:
        nonlocal body, pending_binders
        if not pending_binders:
            return
        body = "∀ " + " ".join(reversed(pending_binders)) + ", " + body
        pending_binders = []

    for hyp in reversed(list(hypotheses or ())):
        text = str(hyp or "").strip()
        if not text:
            continue
        if ":=" in text:
            flush_binders()
            let_text = text.rstrip(";")
            prefix = let_text if let_text.startswith("let ") else f"let {let_text}"
            body = f"{prefix}; {body}"
            continue
        if ":" not in text or "\n" in text or "⊢" in text:
            continue
        pending_binders.append(f"({text})")
    flush_binders()
    return body


def active_root_target_statement(
    dossier_or_targets: Any,
    *,
    require_single: bool = True,
    require_no_hypotheses: bool = False,
    include_hypotheses: bool = True,
) -> str:
    """Return the authoritative Lean-derived active root target text, if unique.

    Active-root extraction rewrites answer-shell PutnamBench goals into the
    actual mathematical target. Downstream prompt, tool, and retrieval paths
    should use this helper instead of rediscovering their own target framing.
    """

    if isinstance(dossier_or_targets, list) or isinstance(dossier_or_targets, tuple):
        raw_targets = list(dossier_or_targets or ())
    else:
        current_frame = getattr(
            dossier_or_targets,
            "active_root_targets_for_current_frame",
            None,
        )
        if callable(current_frame):
            try:
                raw_targets = list(current_frame())
            except Exception:
                raw_targets = []
        else:
            raw_targets = list(
                getattr(dossier_or_targets, "active_root_targets", []) or ()
            )
    targets = [
        dict(item)
        for item in raw_targets
        if isinstance(item, dict)
        and str(item.get("working_target") or item.get("target") or "").strip()
    ]
    if not targets:
        return ""
    if require_single and len(targets) != 1:
        return ""
    rendered: List[str] = []
    for item in targets[:1 if require_single else len(targets)]:
        target = " ".join(
            str(item.get("working_target") or item.get("target") or "").split()
        ).strip()
        if not target:
            continue
        hypotheses = [
            " ".join(str(hyp or "").split()).strip()
            for hyp in list(item.get("hypotheses") or ())
            if str(hyp or "").strip()
        ]
        if hypotheses and require_no_hypotheses:
            return ""
        if include_hypotheses and hypotheses:
            rendered.append(
                " ".join(
                    _active_root_statement_from_hypotheses(
                        target,
                        hypotheses,
                    ).split()
                ).strip()
            )
        else:
            rendered.append(target)
    return " ".join(part for part in rendered if part).strip()


def active_root_equivalence_statements(dossier_or_targets: Any) -> Tuple[str, ...]:
    """Return closed active-root statements for root-equivalence checks."""

    if isinstance(dossier_or_targets, list) or isinstance(dossier_or_targets, tuple):
        raw_targets = list(dossier_or_targets or ())
    else:
        raw_targets = list(
            getattr(dossier_or_targets, "active_root_targets", []) or ()
        )
    statements: List[str] = []
    for item in raw_targets:
        if not isinstance(item, dict):
            continue
        closed = active_root_target_statement(
            [item],
            require_single=True,
            require_no_hypotheses=False,
            include_hypotheses=True,
        )
        if closed:
            statements.append(closed)
    return tuple(dict.fromkeys(statements))


def active_root_targets_match_frame(
    targets: Sequence[Dict[str, Any]],
    *,
    root_statement: str,
    preamble: str,
    helper_blocks: Sequence[str] = (),
    require_helper_context_hash_match: bool = False,
) -> bool:
    if not targets:
        return False
    root_key = canonical_dossier_statement_key(root_statement)
    preamble_key = text_hash(preamble)
    helper_key = text_hash(
        "\n".join(
            sorted(
                str(block or "").strip()
                for block in list(helper_blocks or ())
                if str(block or "").strip()
            )
        )
    )
    for item in list(targets or ()):
        if not _active_root_target_matches_frame(
            item,
            root_key=root_key,
            preamble_key=preamble_key,
            helper_key=helper_key,
            require_helper_context_hash_match=require_helper_context_hash_match,
        ):
            return False
    return True


def _active_root_target_matches_frame(
    item: Any,
    *,
    root_key: str,
    preamble_key: str,
    helper_key: str,
    require_helper_context_hash_match: bool,
) -> bool:
    if not isinstance(item, dict):
        return False
    item_root_key = str(item.get("root_statement_key") or "").strip()
    item_preamble_hash = str(item.get("preamble_hash") or "").strip()
    item_helper_hash = str(item.get("helper_context_hash") or "").strip()
    if not item_root_key or not item_preamble_hash or not item_helper_hash:
        return False
    if item_root_key != root_key or item_preamble_hash != preamble_key:
        return False
    if require_helper_context_hash_match and item_helper_hash != helper_key:
        return False
    return True


def active_root_targets_for_frame(
    dossier_or_targets: Any,
    *,
    root_statement: str,
    preamble: str,
    helper_blocks: Sequence[str] = (),
    require_helper_context_hash_match: bool = False,
) -> List[Dict[str, Any]]:
    if isinstance(dossier_or_targets, list) or isinstance(dossier_or_targets, tuple):
        raw_targets = list(dossier_or_targets or ())
    else:
        raw_targets = list(
            getattr(dossier_or_targets, "active_root_targets", []) or ()
        )
    root_key = canonical_dossier_statement_key(root_statement)
    preamble_key = text_hash(preamble)
    helper_key = text_hash(
        "\n".join(
            sorted(
                str(block or "").strip()
                for block in list(helper_blocks or ())
                if str(block or "").strip()
            )
        )
    )
    return [
        dict(item)
        for item in raw_targets
        if _active_root_target_matches_frame(
            item,
            root_key=root_key,
            preamble_key=preamble_key,
            helper_key=helper_key,
            require_helper_context_hash_match=require_helper_context_hash_match,
        )
    ]


def _dossier_strip_balanced_outer_parens(text: str) -> str:
    s = str(text or "").strip()
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        balanced = True
        for index, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and index != len(s) - 1:
                    balanced = False
                    break
                if depth < 0:
                    balanced = False
                    break
        if not balanced or depth != 0:
            break
        s = s[1:-1].strip()
    return s


def _dossier_find_top_level_comma(text: str) -> int:
    raw = str(text or "")
    depth = 0
    index = 0
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = raw[index]
        if ch in _DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == "," and depth == 0:
            return index
        index += 1
    return -1


def _dossier_top_level_binder_separator_index(
    text: str,
    tokens: Sequence[str],
) -> int:
    raw = str(text or "")
    depth = 0
    index = 0
    matches: List[int] = []
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = raw[index]
        if ch in _DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif depth == 0:
            for token in tokens:
                if raw.startswith(token, index):
                    matches.append(index)
                    break
        index += 1
    return min(matches) if matches else -1


def _dossier_top_level_colon_index(text: str) -> int:
    return _dossier_top_level_binder_separator_index(text, (":",))


def _dossier_lean_identifier_tokens(text: str) -> Tuple[str, ...]:
    raw = str(text or "")
    tokens: List[str] = []
    index = 0
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            if raw.startswith("«", index):
                tokens.append(raw[index:skip_to])
            index = skip_to
            continue
        match = re.match(r"[^\W\d][\w']*", raw[index:], flags=re.UNICODE)
        if match is not None:
            tokens.append(match.group(0))
            index += len(match.group(0))
            continue
        index += 1
    return tuple(tokens)


def _dossier_binder_names_from_chunk(chunk: str) -> Tuple[str, ...]:
    raw = str(chunk or "").strip()
    raw = _dossier_unwrap_binder_group(raw)
    separator_index = _dossier_top_level_binder_separator_index(
        raw,
        (":", *_DOSSIER_RELATION_BINDER_TOKENS),
    )
    if separator_index >= 0:
        raw = raw[:separator_index]
    raw = raw.translate(str.maketrans({ch: " " for ch in "(){}[]⦃⦄⟨⟩"}))
    names: List[str] = []
    for name in _dossier_lean_identifier_tokens(raw):
        if name.lower() in {"forall", "exists", "fun", "by", "let", "in"}:
            continue
        if name not in names:
            names.append(name)
    return tuple(names)


def _dossier_unwrap_binder_group(text: str) -> str:
    raw = str(text or "").strip()
    if len(raw) >= 2:
        closer = _DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE.get(raw[0])
        if closer and raw.endswith(closer):
            return raw[1:-1].strip()
    return raw


def _dossier_binder_group_chunks(chunk: str) -> Tuple[str, ...]:
    """Use the graph's telescope parser for identical binder boundaries.

    In particular, ``x (h : Q x)`` is two binder groups, whereas the
    parentheses in ``x : Fin (n + 1)`` belong to the first group's type.
    """

    return _graph_binder_group_chunks(chunk)


def _dossier_looks_like_proof_premise_type(
    type_text: str,
    binder_names: Sequence[str],
) -> bool:
    clean = _dossier_strip_balanced_outer_parens(str(type_text or "").strip())
    if not clean:
        return False
    compact = " ".join(clean.split()).strip("{}[]")
    lowered = compact.lower()
    def proof_like_binder_name(name: str) -> bool:
        clean_name = str(name or "").strip().lower()
        if clean_name == "_":
            return True
        name_key = clean_name.lstrip("_")
        return bool(name_key) and name_key.startswith(
            (
                "h",
                "hyp",
                "this",
                "proof",
                "assump",
                "premise",
                "cond",
                "given",
            )
        )

    hyp_like_name = any(
        proof_like_binder_name(name) for name in binder_names
    )
    if lowered in {
        "nat",
        "ℕ",
        "int",
        "ℤ",
        "rat",
        "ℚ",
        "real",
        "ℝ",
        "bool",
        "prop",
        "type",
    }:
        return False
    if re.fullmatch(r"(?:Type|Sort|Prop)(?:\s+\d+|\s+u)?", compact):
        return False
    if re.match(
        r"^(?:Set|Finset|List|Multiset|Option|Array|Seq|Fin|ZMod|Polynomial|"
        r"Matrix|Vector|Subtype|ULift|PLift|WithTop|WithBot|OrderDual|"
        r"Additive|Multiplicative|Ideal|Submodule|Subgroup|Subsemiring|"
        r"Subring|Subfield|Equiv|LinearEquiv|RingEquiv|OrderIso|Type|Sort)\b",
        compact,
    ):
        return False
    if re.match(
        r"^(?:Fintype|Finite|DecidableEq|Inhabited|Subsingleton|Unique|"
        r"Group|CommGroup|AddGroup|AddCommGroup|Monoid|CommMonoid|"
        r"AddMonoid|AddCommMonoid|Semigroup|CommSemigroup|Ring|CommRing|"
        r"Semiring|CommSemiring|Field|DivisionRing|LinearOrder|PartialOrder|"
        r"Preorder|Lattice|DistribLattice|LinearOrderedRing|"
        r"LinearOrderedField|OrderedRing|OrderedSemiring|TopologicalSpace|"
        r"MetricSpace|NormedRing|NormedField|NormedSpace|Module|Algebra)\b",
        compact,
    ):
        return False
    if "→" in compact or "->" in compact:
        arrow_parts = _dossier_split_top_level_implications(compact)
        codomain = arrow_parts[-1] if arrow_parts else compact
        codomain = _dossier_strip_balanced_outer_parens(codomain).strip()
        codomain_lower = codomain.lower()
        type_like_arrow = len(arrow_parts) >= 2 and all(
            _dossier_looks_like_parameter_type_part(part) for part in arrow_parts
        )
        if (
            type_like_arrow
            or codomain_lower in {"prop", "type", "sort"}
            or codomain_lower in {"nat", "int", "rat", "real", "bool"}
            or codomain in {"ℕ", "ℤ", "ℚ", "ℝ", "Nat", "Int", "Rat", "Real", "Bool"}
            or re.match(
                r"^(?:Set|Finset|List|Multiset|Option|Array|Seq|Fin|ZMod|"
                r"Polynomial|Matrix|Vector|Subtype|ULift|PLift|WithTop|WithBot|"
                r"OrderDual|Additive|Multiplicative|Ideal|Submodule|Subgroup|"
                r"Subsemiring|Subring|Subfield|Equiv|LinearEquiv|RingEquiv|"
                r"OrderIso)\b",
                codomain,
            )
            or re.fullmatch(r"(?:Type|Sort|Prop)(?:\s+\d+|\s+u)?", codomain)
            or (
                not hyp_like_name
                and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", codomain)
            )
        ):
            return False
    if any(symbol in compact for symbol in ("=", "<", ">", "≤", "≥", "≠", "∈", "∉", "∣")):
        return True
    if any(symbol in compact for symbol in ("→", "->", "↔", "¬", "∧", "∨", "∀", "∃")):
        return True
    if re.search(
        r"\b(?:Odd|Even|Prime|Nat\.Prime|Irreducible|Nonempty|Pairwise|"
        r"Monotone|StrictMono|Injective|Surjective|Bijective|Continuous)\b",
        compact,
    ):
        return True
    if re.fullmatch(r"[A-Z][A-Za-z0-9_'.]*(?:\s+.+)?", compact):
        return True
    if hyp_like_name and re.fullmatch(
        r"[A-Za-z_][A-Za-z0-9_'.]*(?:\s+.+)+",
        compact,
    ):
        return True
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", compact):
        return hyp_like_name
    return False


def _dossier_looks_like_parameter_type_part(text: str) -> bool:
    compact = _dossier_strip_balanced_outer_parens(
        " ".join(str(text or "").split()).strip("{}[]")
    )
    lowered = compact.lower()
    if lowered in {"nat", "int", "rat", "real", "bool", "prop", "type", "sort"}:
        return True
    if compact in {"ℕ", "ℤ", "ℚ", "ℝ", "Nat", "Int", "Rat", "Real", "Bool"}:
        return True
    if re.fullmatch(r"(?:Type|Sort|Prop)(?:\s+\d+|\s+u)?", compact):
        return True
    return bool(
        re.match(
            r"^(?:Set|Finset|List|Multiset|Option|Array|Seq|Fin|ZMod|"
            r"Polynomial|Matrix|Vector|Subtype|ULift|PLift|WithTop|WithBot|"
            r"OrderDual|Additive|Multiplicative|Ideal|Submodule|Subgroup|"
            r"Subsemiring|Subring|Subfield|Equiv|LinearEquiv|RingEquiv|"
            r"OrderIso)\b",
            compact,
        )
    )


def _dossier_strip_leading_forall_binders(text: str) -> str:
    s = _dossier_strip_balanced_outer_parens(text)
    while True:
        quantifier_match = re.match(r"^(?:∀|forall\b)\s*", s)
        if quantifier_match is None:
            break
        comma = _dossier_find_top_level_comma(s)
        if comma < 0:
            break
        s = _dossier_strip_balanced_outer_parens(s[comma + 1 :])
    return s


def _dossier_strip_leading_forall_binders_with_names_and_premises(
    text: str,
) -> Tuple[str, Tuple[str, ...], Tuple[str, ...]]:
    return graph_statement_leading_contract(text)


def _dossier_strip_leading_forall_binders_with_names(
    text: str,
) -> Tuple[str, Tuple[str, ...]]:
    s, names, _premises = _dossier_strip_leading_forall_binders_with_names_and_premises(
        text
    )
    return s, names


def _dossier_statement_premises_and_conclusion(
    statement: str,
) -> Tuple[Tuple[str, ...], str, Tuple[str, ...]]:
    return graph_statement_premises_and_conclusion(statement)


def _dossier_nonproof_parameter_profile(statement: str) -> Tuple[str, ...]:
    """Return normalized non-proof binder types in the leading theorem frame."""

    return graph_statement_nonproof_parameter_profile(statement)


def _dossier_statement_root_equivalent(
    statement: str,
    root_statement: str,
    *,
    active_target_statements: Sequence[str] = (),
) -> bool:
    """Dossier-safe root equivalence that rejects extra non-proof parameters."""

    stmt = str(statement or "").strip()
    root = str(root_statement or "").strip()
    if not stmt or not root:
        return False
    stmt_profile = _dossier_nonproof_parameter_profile(stmt)
    candidates = [root, *[str(item or "").strip() for item in active_target_statements]]
    for candidate in candidates:
        if not candidate:
            continue
        if not graph_statement_root_equivalent(stmt, candidate):
            continue
        if stmt_profile == _dossier_nonproof_parameter_profile(candidate):
            return True
    return False


def _dossier_split_top_level_implications(statement: str) -> List[str]:
    return [
        _dossier_strip_balanced_outer_parens(part)
        for part in split_lean_top_level_implications(statement)
    ]


def _dossier_split_top_level_iffs(statement: str) -> List[str]:
    text = str(statement or "")
    parts: List[str] = []
    start = 0
    depth = 0
    index = 0
    while index < len(text):
        skip_to = _lean_lexical_skip_end(text, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = text[index]
        if ch in _DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == "↔" and depth == 0:
            parts.append(text[start:index].strip())
            start = index + 1
        elif depth == 0 and text.startswith("<->", index):
            parts.append(text[start:index].strip())
            start = index + 3
            index += 2
        index += 1
    parts.append(text[start:].strip())
    return [
        _dossier_strip_balanced_outer_parens(part)
        for part in parts
        if part.strip()
    ]


def _dossier_split_top_level_conjunctions(text: str) -> List[str]:
    parts: List[str] = []
    start = 0
    depth = 0
    value = str(text or "")
    index = 0
    while index < len(value):
        skip_to = _lean_lexical_skip_end(value, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = value[index]
        if ch in _DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == "∧" and depth == 0:
            parts.append(value[start:index].strip())
            start = index + 1
        index += 1
    parts.append(value[start:].strip())
    return [
        _dossier_strip_balanced_outer_parens(part)
        for part in parts
        if part.strip()
    ]


def _dossier_contract_norm(text: str) -> str:
    stripped = _dossier_strip_leading_forall_binders(text)
    stripped = _dossier_normalize_numeric_casts_for_contract(stripped)
    stripped = re.sub(r"\((\d+)\s*:\s*[^()]+\)", r"\1", stripped)
    return re.sub(r"\s+", "", stripped)


def _dossier_quantifier_bound_names(text: str) -> Tuple[str, ...]:
    names: List[str] = []
    for match in re.finditer(r"(?:[∀∃]|forall|exists)\s*([^,]+),", str(text or "")):
        names.extend(_dossier_binder_names_from_chunk(match.group(1)))
    return tuple(dict.fromkeys(names))


def _dossier_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'"


def _dossier_top_level_quantifier_token_len(text: str, index: int) -> int:
    raw = str(text or "")
    ch = raw[index] if 0 <= index < len(raw) else ""
    if ch in {"∀", "∃"}:
        return 1
    for token in ("forall", "exists"):
        end = index + len(token)
        if not raw.startswith(token, index):
            continue
        before_ok = index == 0 or not _dossier_ident_char(raw[index - 1])
        after_ok = end >= len(raw) or not _dossier_ident_char(raw[end])
        if before_ok and after_ok:
            return len(token)
    return 0


def _dossier_matching_group_index(text: str, start: int) -> int:
    raw = str(text or "")
    opener = raw[start] if 0 <= start < len(raw) else ""
    expected = _DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE.get(opener)
    if expected is None:
        return -1
    stack: List[str] = [expected]
    index = start + 1
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = raw[index]
        if ch in _DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE:
            stack.append(_DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE[ch])
        elif stack and ch == stack[-1]:
            stack.pop()
            if not stack:
                return index
        elif ch in _DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE.values():
            return -1
        index += 1
    return -1


_DOSSIER_ALPHA_BOUND_PLACEHOLDER_RE = re.compile(r"^__bound\d+__$")
_DOSSIER_ALPHA_FREE_IDENTIFIER_ESCAPE_PREFIX = "\0mini-alpha-free-identifier:"


def _dossier_contract_alpha_identifier_token(
    token: str,
    mapping: Mapping[str, str],
) -> str:
    if token in mapping:
        return mapping[token]
    if _DOSSIER_ALPHA_BOUND_PLACEHOLDER_RE.fullmatch(token):
        return f"{_DOSSIER_ALPHA_FREE_IDENTIFIER_ESCAPE_PREFIX}{token}\0"
    return token


def _dossier_contract_alpha_norm(
    text: str,
    *,
    context_bound_names: Sequence[str] = (),
) -> str:
    stripped, leading_names = _dossier_strip_leading_forall_binders_with_names(text)
    bound_names = tuple(
        dict.fromkeys(
            tuple(
                str(name or "").strip()
                for name in context_bound_names
                if str(name or "").strip()
            )
            + leading_names
        )
    )
    mapping = {name: f"__bound{idx}__" for idx, name in enumerate(bound_names)}

    stripped = _dossier_normalize_numeric_casts_for_contract(stripped)
    stripped = re.sub(r"\((\d+)\s*:\s*[^()]+\)", r"\1", stripped)
    normalized = _dossier_contract_alpha_replace_scoped(stripped, mapping)
    return re.sub(r"\s+", "", normalized)


def _dossier_contract_alpha_replace_scoped(
    text: str,
    mapping: Mapping[str, str],
) -> str:
    raw = str(text or "")
    out: List[str] = []
    index = 0
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None:
            token = raw[index:skip_to]
            out.append(mapping.get(token, token) if raw.startswith("«", index) else token)
            index = skip_to
            continue
        ch = raw[index]
        if ch in _DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE:
            end = _dossier_matching_group_index(raw, index)
            if end >= 0:
                out.append(ch)
                out.append(
                    _dossier_contract_alpha_replace_scoped(
                        raw[index + 1 : end],
                        mapping,
                    )
                )
                out.append(raw[end])
                index = end + 1
                continue
        quantifier_len = _dossier_top_level_quantifier_token_len(raw, index)
        if quantifier_len:
            tail_start = index + quantifier_len
            comma = _dossier_find_top_level_comma(raw[tail_start:])
            if comma >= 0:
                binder = raw[tail_start : tail_start + comma]
                body = raw[tail_start + comma + 1 :]
                local_mapping = dict(mapping)
                next_index = len(local_mapping)
                for binder_group in _dossier_binder_group_chunks(binder):
                    for name in _dossier_binder_names_from_chunk(binder_group):
                        local_mapping[name] = f"__bound{next_index}__"
                        next_index += 1
                out.append(raw[index : index + quantifier_len])
                out.append(
                    _dossier_contract_alpha_replace_scoped(binder, local_mapping)
                )
                out.append(",")
                out.append(
                    _dossier_contract_alpha_replace_scoped(body, local_mapping)
                )
                return "".join(out)
        match = re.match(r"[A-Za-z_][A-Za-z0-9_']*", raw[index:])
        if match is not None:
            token = match.group(0)
            out.append(_dossier_contract_alpha_identifier_token(token, mapping))
            index += len(token)
            continue
        out.append(raw[index])
        index += 1
    return "".join(out)


def _dossier_matching_paren_index(text: str, start: int) -> int:
    depth = 0
    for index in range(start, len(text)):
        ch = text[index]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return index
        if depth < 0:
            return -1
    return -1


def _dossier_normalize_numeric_casts_for_contract(text: str) -> str:
    numeric_type_re = re.compile(r"(?:ℚ|Rat|ℝ|Real|ℤ|Int|ℕ|Nat)")

    def normalize(value: str) -> str:
        out: List[str] = []
        index = 0
        while index < len(value):
            if value[index] != "(":
                out.append(value[index])
                index += 1
                continue
            end = _dossier_matching_paren_index(value, index)
            if end < 0:
                out.append(value[index])
                index += 1
                continue
            body = normalize(value[index + 1 : end])
            colon = _dossier_top_level_colon_index(body)
            if colon >= 0:
                expr = body[:colon].strip()
                type_text = _dossier_strip_balanced_outer_parens(
                    body[colon + 1 :].strip()
                )
                if expr and re.search(r"\d", expr) and numeric_type_re.fullmatch(type_text):
                    out.append(_dossier_strip_balanced_outer_parens(expr))
                    index = end + 1
                    continue
            out.append("(")
            out.append(body)
            out.append(")")
            index = end + 1
        return "".join(out)

    return normalize(str(text or ""))


def _dossier_split_top_level_equality(text: str) -> Tuple[str, str]:
    stripped = _dossier_strip_balanced_outer_parens(
        _dossier_strip_leading_forall_binders(text)
    )
    depth = 0
    index = 0
    while index < len(stripped):
        skip_to = _lean_lexical_skip_end(stripped, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = stripped[index]
        if ch in _DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _DOSSIER_LEAN_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif (
            ch == "="
            and depth == 0
            and (index == 0 or stripped[index - 1] not in "<>!:")
            and (index + 1 >= len(stripped) or stripped[index + 1] not in "=>")
        ):
            return stripped[:index].strip(), stripped[index + 1 :].strip()
        index += 1
    return "", ""


def _dossier_root_conclusion_candidates(
    root_statement: str,
) -> List[Tuple[str, Tuple[str, ...]]]:
    candidates: List[Tuple[str, Tuple[str, ...]]] = []
    seen: Set[str] = set()

    def add_candidate(candidate_text: str, candidate_bound_names: Tuple[str, ...]) -> None:
        key = _dossier_contract_alpha_norm(
            candidate_text,
            context_bound_names=candidate_bound_names,
        )
        if key and key not in seen:
            seen.add(key)
            candidates.append((candidate_text, candidate_bound_names))

    body, bound_names = _dossier_strip_leading_forall_binders_with_names(
        str(root_statement or "")
    )
    parts = _dossier_split_top_level_implications(body)
    conclusion = parts[-1] if parts else body
    conclusion_parts = _dossier_split_top_level_iffs(conclusion)
    for candidate in conclusion_parts or [conclusion]:
        candidate, candidate_names = _dossier_strip_leading_forall_binders_with_names(
            candidate
        )
        all_names = tuple(dict.fromkeys(bound_names + candidate_names))
        add_candidate(candidate, all_names)
        candidate_implications = _dossier_split_top_level_implications(candidate)
        if len(candidate_implications) >= 2:
            add_candidate(candidate_implications[-1], all_names)
    return candidates


def _dossier_statements_root_adjacent(
    conclusion: str,
    root_statement: str,
    *,
    conclusion_bound_names: Sequence[str] = (),
) -> bool:
    conclusion_norm = _dossier_contract_alpha_norm(
        conclusion,
        context_bound_names=conclusion_bound_names,
    )
    if not conclusion_norm:
        return False
    for candidate, root_bound_names in _dossier_root_conclusion_candidates(
        root_statement
    ):
        root_norm = _dossier_contract_alpha_norm(
            candidate,
            context_bound_names=root_bound_names,
        )
        if root_norm and conclusion_norm == root_norm:
            return True
    return False


def _dossier_statement_is_negative_evidence(statement: str) -> bool:
    body, _names = _dossier_strip_leading_forall_binders_with_names(statement)
    compact = " ".join(str(body or "").split()).strip()
    if not compact:
        return False
    return bool(
        compact == "False"
        or compact.startswith("False ")
        or compact.startswith("¬")
        or compact.startswith("Not ")
    )


def _dossier_statement_is_existential_counterexample(
    statement: str,
    root_statement: str,
) -> bool:
    """Recognize ``Exists inputs, premises and not root_conclusion`` facts."""

    body = _dossier_strip_balanced_outer_parens(statement)
    functional_exists = re.match(
        r"^Exists\s+fun\s+(.+?)\s*=>\s*(.+)$",
        body,
        flags=re.DOTALL,
    )
    if functional_exists is not None:
        binder = str(functional_exists.group(1) or "").strip()
        predicate = str(functional_exists.group(2) or "").strip()
        if binder and predicate:
            body = f"∃ {binder}, {predicate}"
    existential_names: List[str] = []
    existential_binder_chunks: List[str] = []
    found_exists = False
    while True:
        quantifier_match = re.match(r"^(?:∃|exists\b)\s*", body)
        if quantifier_match is None:
            break
        comma = _dossier_find_top_level_comma(body)
        if comma < 0:
            return False
        found_exists = True
        binder_chunk = body[quantifier_match.end() : comma]
        existential_binder_chunks.append(binder_chunk.strip())
        existential_names.extend(_dossier_binder_names_from_chunk(binder_chunk))
        body = _dossier_strip_balanced_outer_parens(body[comma + 1 :])
    if not found_exists or not existential_names:
        return False
    existential_frame = " ".join(
        f"∀ {chunk}," for chunk in existential_binder_chunks if chunk
    ) + " True"
    if _dossier_nonproof_parameter_profile(
        existential_frame
    ) != _dossier_nonproof_parameter_profile(root_statement):
        return False
    root_body, root_bound_names, root_binder_premises = (
        _dossier_strip_leading_forall_binders_with_names_and_premises(
            root_statement
        )
    )
    root_implication_parts = _dossier_split_top_level_implications(root_body)
    required_root_premises = [
        *root_binder_premises,
        *root_implication_parts[:-1],
    ]
    existential_conjuncts = _dossier_split_top_level_conjunctions(body)
    for premise in required_root_premises:
        premise_key = canonical_dossier_statement_key(premise)
        premise_norm = _dossier_contract_alpha_norm(
            premise,
            context_bound_names=root_bound_names,
        )
        if not any(
            (
                premise_key
                and premise_key == canonical_dossier_statement_key(conjunct)
            )
            or (
                premise_norm
                and premise_norm
                == _dossier_contract_alpha_norm(
                    conjunct,
                    context_bound_names=tuple(existential_names),
                )
            )
            for conjunct in existential_conjuncts
        ):
            return False
    root_candidates = _dossier_root_conclusion_candidates(root_statement)
    root_conclusion = (
        root_implication_parts[-1]
        if root_implication_parts
        else root_body
    )
    if len(_dossier_split_top_level_iffs(root_conclusion)) >= 2:
        # A witness refutes an equivalence by refuting the equivalence itself,
        # not merely by negating one of two potentially identical sides.
        root_candidates = [(root_conclusion, root_bound_names)]
    if not root_candidates:
        return False
    for conjunct in existential_conjuncts:
        negative_inner = ""
        stripped = _dossier_strip_balanced_outer_parens(conjunct)
        if stripped.startswith("¬"):
            negative_inner = stripped[1:].strip()
        elif stripped.startswith("Not"):
            tail = stripped[3:]
            if tail and not (tail[0].isalnum() or tail[0] in "_'"):
                negative_inner = tail.strip()
        if not negative_inner:
            implication_parts = _dossier_split_top_level_implications(stripped)
            if (
                len(implication_parts) == 2
                and canonical_dossier_statement_key(implication_parts[-1])
                == canonical_dossier_statement_key("False")
            ):
                negative_inner = implication_parts[0]
        if not negative_inner:
            equality_form = stripped.replace("≠", "=", 1)
            lhs, rhs = _dossier_split_top_level_equality(equality_form)
            if lhs and rhs and equality_form != stripped:
                negative_inner = f"{lhs} = {rhs}"
        if not negative_inner:
            continue
        negative_surface_key = canonical_dossier_statement_key(
            _dossier_strip_balanced_outer_parens(negative_inner)
        )
        if any(
            negative_surface_key
            and negative_surface_key == canonical_dossier_statement_key(candidate)
            for candidate, _root_names in root_candidates
        ):
            return True
        negative_norm = _dossier_contract_alpha_norm(
            _dossier_strip_balanced_outer_parens(negative_inner),
            context_bound_names=tuple(existential_names),
        )
        if any(
            negative_norm
            and negative_norm
            == _dossier_contract_alpha_norm(
                candidate,
                context_bound_names=root_names,
            )
            for candidate, root_names in root_candidates
        ):
            return True
    return False


def _dossier_negated_statement_key(statement: str) -> str:
    """Return the canonical key for ``P`` when ``statement`` refutes ``P``."""

    premises, conclusion, _bound_names = _dossier_statement_premises_and_conclusion(
        statement
    )
    if (
        len(premises) == 1
        and _dossier_statement_is_negative_evidence(conclusion)
    ):
        return canonical_dossier_statement_key(premises[0])
    body, _names = _dossier_strip_leading_forall_binders_with_names(statement)
    compact = " ".join(str(body or "").split()).strip()
    if not compact:
        return ""
    inner = ""
    if compact.startswith("¬"):
        inner = compact[1:].strip()
    elif compact.startswith("Not "):
        inner = compact[4:].strip()
    if not inner:
        return ""
    inner = _dossier_strip_balanced_outer_parens(inner)
    return canonical_dossier_statement_key(inner)


def _dossier_statement_has_negative_conclusion(statement: str) -> bool:
    _premises, conclusion, _bound_names = _dossier_statement_premises_and_conclusion(
        statement
    )
    return _dossier_statement_is_negative_evidence(conclusion)


def _dossier_support_candidates(
    statement: str,
    *,
    include_implication_premises: bool = False,
    premises_are_assumptions: bool = False,
) -> List[Tuple[str, Tuple[str, ...]]]:
    candidates: List[Tuple[str, Tuple[str, ...]]] = []
    seen: Set[Tuple[str, Tuple[str, ...]]] = set()

    def add_candidate(statement_text: str, names: Sequence[str]) -> None:
        candidate = (str(statement_text or "").strip(), tuple(names or ()))
        if candidate[0] and candidate not in seen:
            seen.add(candidate)
            candidates.append(candidate)

    def add_assumption_candidate(
        statement_text: str,
        names: Sequence[str],
    ) -> None:
        item_body, item_names = _dossier_strip_leading_forall_binders_with_names(
            statement_text
        )
        item_bound_names = tuple(dict.fromkeys(tuple(names or ()) + item_names))
        add_candidate(item_body, item_bound_names)
        if (
            "→" in item_body
            or "->" in item_body
            or "∀" in item_body
            or "∃" in item_body
        ):
            items = [item_body]
        else:
            items = _dossier_split_top_level_conjunctions(item_body)
        for item in items:
            conjunct_body, conjunct_names = (
                _dossier_strip_leading_forall_binders_with_names(item)
            )
            add_candidate(
                conjunct_body,
                tuple(dict.fromkeys(item_bound_names + conjunct_names)),
            )

    body, bound_names, binder_premises = (
        _dossier_strip_leading_forall_binders_with_names_and_premises(
            str(statement or "")
        )
    )
    if premises_are_assumptions:
        for premise in binder_premises:
            add_assumption_candidate(premise, bound_names)
    parts = _dossier_split_top_level_implications(body)
    conclusion = parts[-1] if parts else body
    if (
        premises_are_assumptions
        and include_implication_premises
        and len(parts) >= 2
    ):
        selected = parts[:-1]
    elif include_implication_premises:
        selected = []
    elif binder_premises:
        selected = []
    else:
        selected = [body]
    if premises_are_assumptions and include_implication_premises:
        iff_parts = _dossier_split_top_level_iffs(conclusion)
        if len(iff_parts) >= 2:
            selected.extend(iff_parts)
            for iff_part in iff_parts:
                iff_body, iff_names, iff_binder_premises = (
                    _dossier_strip_leading_forall_binders_with_names_and_premises(
                        iff_part
                    )
                )
                iff_bound_names = tuple(dict.fromkeys(bound_names + iff_names))
                for premise in iff_binder_premises:
                    add_assumption_candidate(premise, iff_bound_names)
                iff_implication_parts = _dossier_split_top_level_implications(iff_body)
                if len(iff_implication_parts) >= 2:
                    for premise in iff_implication_parts[:-1]:
                        premise_body, premise_names = (
                            _dossier_strip_leading_forall_binders_with_names(premise)
                        )
                        add_candidate(
                            premise_body,
                            tuple(dict.fromkeys(iff_bound_names + premise_names)),
                        )
    for item in selected:
        add_assumption_candidate(item, bound_names)
    return candidates


def _dossier_support_contains(
    premise: str,
    support_candidates: Iterable[Tuple[str, Tuple[str, ...]]],
    *,
    premise_bound_names: Sequence[str] = (),
) -> bool:
    premise_key = canonical_dossier_statement_key(premise)
    premise_norm = _dossier_contract_norm(premise)
    premise_alpha_norm = _dossier_contract_alpha_norm(
        premise,
        context_bound_names=premise_bound_names,
    )
    for support, support_bound_names in support_candidates:
        if premise_key and premise_key == canonical_dossier_statement_key(support):
            return True
        if premise_norm and premise_norm == _dossier_contract_norm(support):
            return True
        support_alpha_norm = _dossier_contract_alpha_norm(
            support,
            context_bound_names=support_bound_names,
        )
        if premise_alpha_norm and premise_alpha_norm == support_alpha_norm:
            return True
    return False


def normalize_scratch_code_for_registry(code: str) -> str:
    """Compact scratch proof code for durable accepted-check matching."""

    text = str(code or "").strip()
    text = re.sub(r"^```(?:lean)?\s*", "", text, flags=re.IGNORECASE)
    text = re.sub(r"\s*```$", "", text)
    text = " ".join(text.split())
    text = re.sub(r"\s*(:=|=>|←|↦)\s*", r"\1", text)
    text = re.sub(r"\s*([()\[\]{},:;])\s*", r"\1", text)
    return text[:4000]


def clone_verified_helper(item: "VerifiedHelper") -> "VerifiedHelper":
    """Clone a helper record without sharing mutable support metadata."""

    return replace(
        item,
        support_names=list(item.support_names),
        support_source_hashes=dict(getattr(item, "support_source_hashes", {}) or {}),
        replay_context_names=list(
            getattr(item, "replay_context_names", []) or []
        ),
        replay_context_source_hashes=dict(
            getattr(item, "replay_context_source_hashes", {}) or {}
        ),
        quality_tags=list(getattr(item, "quality_tags", []) or []),
        open_premise_statement_keys=list(
            getattr(item, "open_premise_statement_keys", []) or []
        ),
        open_premise_statements=list(
            getattr(item, "open_premise_statements", []) or []
        ),
        closed_open_premise_statements=list(
            getattr(item, "closed_open_premise_statements", []) or []
        ),
    )


def propagate_proposed_helpers(
    parent: "ProofDossier",
    child: "ProofDossier",
    *,
    record_graph: bool = True,
) -> int:
    """Carry banked ``proposed_helpers`` from ``child`` back to ``parent``.

    Used on failure-path return from isolated session boundaries
    (sample/branch fan-outs and recursive helper sub-sessions): the success
    path is handled by
    ``_copy_dossier_contents``'s wholesale clobber; this function is
    the failure-side analogue.

    Semantics:
    - Re-uses ``record_proposed_helper`` so the answer-unsafe filter
      and idempotent-statement-update applies uniformly. A child
      proposal with the same name but a fresher statement OVERWRITES
      the parent's stale entry (matches success-path clobber). This
      closes a re-entrancy gap where consecutive isolated attempts would
      otherwise lose the correction emitted by the later attempt.
    - Skips silently when ``parent is child``.
    - Returns the count of helpers actually applied so callers can
      log / trace.
    """

    if parent is child:
        return 0
    propagate_invalidated_statements(parent, child, record_graph=record_graph)
    if not getattr(child, "proposed_helpers", None):
        return 0
    applied = 0
    for name, item in dict(child.proposed_helpers).items():
        source = str(getattr(item, "source", "") or "")
        if not source:
            continue
        result = parent.record_proposed_helper(
            source,
            phase=str(getattr(item, "phase", "") or ""),
            turn_index=int(getattr(item, "turn_index", 0) or 0),
        )
        if result is not None:
            applied += 1
    return applied


_CERTIFICATE_REPLAY_DISPOSITION_SCHEMA = 1


def _certificate_replay_disposition_id(
    certificate_hash: str, environment_hash: str, policy_hash: str
) -> str:
    from .mini_falsification.model import content_hash
    return content_hash(
        {
            "certificate_hash": str(certificate_hash or ""),
            "environment_hash": str(environment_hash or ""),
            "policy_hash": str(policy_hash or ""),
        }
    )


def _certificate_replay_disposition_is_valid(data: Any) -> bool:
    from .mini_falsification.model import content_hash

    if not isinstance(data, Mapping):
        return False
    record = dict(data)
    claimed_hash = str(record.pop("disposition_hash", "") or "")
    certificate_hash = str(record.get("certificate_hash") or "")
    environment_hash = str(record.get("environment_hash") or "")
    policy_hash = str(record.get("policy_hash") or "")
    return bool(
        int(record.get("schema_version") or 0)
        == _CERTIFICATE_REPLAY_DISPOSITION_SCHEMA
        and str(record.get("status") or "") == "definitive_rejection"
        and re.fullmatch(r"[0-9a-f]{64}", certificate_hash)
        and re.fullmatch(r"[0-9a-f]{64}", environment_hash)
        and re.fullmatch(r"[0-9a-f]{64}", policy_hash)
        and re.fullmatch(r"[0-9a-f]{64}", claimed_hash)
        and content_hash(record) == claimed_hash
    )


_FALSIFICATION_CURSOR_IDENTITY_KEYS = (
    "plan_hash",
    "catalog_hash",
    "domain_size",
)
_GRAPH_CURSOR_REQUIRED_IDENTITY_KEYS = (
    "cursor_schema",
    "plan_hash",
    "catalog_hash",
    "domain_size",
)
_RIGHT_PI_CURSOR_REQUIRED_IDENTITY_KEYS = (
    "cursor_schema",
    "plan_hash",
    "domain_size",
)
_FALSIFICATION_CURSOR_ENGINES = frozenset(
    {
        "finite",
        "numeric",
        "exact_algebra",
        "function",
        "graph",
        "sat_smt",
        "property",
    }
)
_BOUNDED_FALSIFICATION_CURSOR_ENGINES = frozenset(
    {
        "finite",
        "numeric",
        "exact_algebra",
        "function",
        "graph",
        "sat_smt",
    }
)


def _validated_falsification_cursor(
    data: Any,
    *,
    engine: str = "",
) -> Optional[Dict[str, Any]]:
    """Return a bounded cursor copied from an integrity-validated report.

    The report hash authenticates the envelope, but cursor fields still need
    semantic validation before they may advance durable search progress.
    """

    if not isinstance(data, Mapping) or not data:
        return None
    cursor = copy.deepcopy(dict(data))
    raw_index = cursor.get("next_index")
    if not isinstance(raw_index, int) or isinstance(raw_index, bool):
        return None
    next_index = raw_index
    if next_index < 0:
        return None
    engine_name = str(engine or "").strip()
    if engine_name not in _FALSIFICATION_CURSOR_ENGINES:
        return None
    # Applicability is recomputed from the typed statement on every service
    # call.  Historical bare suppression bits have no statement/environment/
    # plan binding and must never become durable search authority.
    if "lane_unavailable" in cursor:
        return None
    raw_domain_size = cursor.get("domain_size")
    if raw_domain_size is not None:
        if engine_name not in _BOUNDED_FALSIFICATION_CURSOR_ENGINES:
            return None
        if not isinstance(raw_domain_size, int) or isinstance(raw_domain_size, bool):
            return None
        domain_size = raw_domain_size
        if domain_size < 0 or next_index > domain_size:
            return None
    if "exhausted" in cursor:
        if not (
            cursor.get("exhausted") is True
            and raw_domain_size is not None
            and next_index == raw_domain_size
        ):
            return None
    raw_phase = cursor.get("phase")
    if raw_phase is not None:
        if not (
            engine_name == "graph"
            and raw_phase
            in {"unlabeled_probe", "labeled_complete", "exhausted"}
        ):
            return None
        if raw_phase == "exhausted" and not (
            raw_domain_size is not None and next_index == raw_domain_size
        ):
            return None
    raw_lane_quanta = cursor.get("lane_quanta")
    if raw_lane_quanta is not None and not (
        isinstance(raw_lane_quanta, int)
        and not isinstance(raw_lane_quanta, bool)
        and raw_lane_quanta >= 0
    ):
        return None
    raw_plan_hash = cursor.get("plan_hash")
    if raw_plan_hash is not None and not (
        isinstance(raw_plan_hash, str)
        and re.fullmatch(r"[0-9a-f]{64}", raw_plan_hash)
        and engine_name in {"graph", "sat_smt", "function"}
    ):
        return None
    raw_catalog_hash = cursor.get("catalog_hash")
    if raw_catalog_hash is not None and not (
        isinstance(raw_catalog_hash, str)
        and re.fullmatch(r"[0-9a-f]{64}", raw_catalog_hash)
        and engine_name == "graph"
    ):
        return None
    if engine_name == "sat_smt" and raw_plan_hash is not None:
        # Native SMT has one deterministic query per plan. Bool enumeration
        # uses the ordinary domain/index cursor and deliberately has no plan
        # hash, so legacy/index-only Bool cursors remain valid.
        if next_index != 1 or raw_domain_size is not None:
            return None
    if engine_name == "graph":
        present_identity_keys = {
            key
            for key in _GRAPH_CURSOR_REQUIRED_IDENTITY_KEYS
            if cursor.get(key) is not None
        }
        if present_identity_keys:
            if present_identity_keys != set(_GRAPH_CURSOR_REQUIRED_IDENTITY_KEYS):
                return None
            if cursor.get("cursor_schema") != GRAPH_PLAN_CURSOR_SCHEMA:
                return None
            if not (
                isinstance(cursor.get("plan_hash"), str)
                and re.fullmatch(r"[0-9a-f]{64}", cursor["plan_hash"])
                and isinstance(cursor.get("catalog_hash"), str)
                and re.fullmatch(r"[0-9a-f]{64}", cursor["catalog_hash"])
                and isinstance(cursor.get("domain_size"), int)
                and not isinstance(cursor.get("domain_size"), bool)
                and int(cursor["domain_size"]) > 0
            ):
                return None
    if engine_name == "function" and (
        raw_plan_hash is not None or cursor.get("cursor_schema") is not None
    ):
        present_identity_keys = {
            key
            for key in _RIGHT_PI_CURSOR_REQUIRED_IDENTITY_KEYS
            if cursor.get(key) is not None
        }
        if present_identity_keys != set(_RIGHT_PI_CURSOR_REQUIRED_IDENTITY_KEYS):
            return None
        if cursor.get("cursor_schema") not in {
            RIGHT_PI_LEGACY_PLAN_CURSOR_SCHEMA,
            RIGHT_PI_OLDER_PLAN_CURSOR_SCHEMA,
            RIGHT_PI_PREVIOUS_PLAN_CURSOR_SCHEMA,
            RIGHT_PI_RECENT_PLAN_CURSOR_SCHEMA,
            RIGHT_PI_PLAN_CURSOR_SCHEMA,
        }:
            return None
        if not (
            isinstance(cursor.get("domain_size"), int)
            and not isinstance(cursor.get("domain_size"), bool)
            and int(cursor["domain_size"]) > 0
        ):
            return None
    recipe_disposition = cursor.get("recipe_repair_disposition")
    if (
        recipe_disposition is not None
        and engine_name == "function"
        and cursor.get("cursor_schema") != RIGHT_PI_PLAN_CURSOR_SCHEMA
    ):
        # The candidate/plan identity changed across the schedule-schema
        # upgrade, so an old recipe receipt cannot suppress a fresh replay.
        # Preserve its validated search index and let the current engine migrate;
        # only the obsolete recipe metadata is discarded.
        cursor.pop("recipe_repair_disposition", None)
        recipe_disposition = None
    if recipe_disposition is not None and not (
        engine_name == "function"
        and right_pi_recipe_repair_disposition_is_valid(
            recipe_disposition,
            cursor=cursor,
        )
    ):
        return None
    return cursor


def _recipe_repair_cursor_matches_finding(
    finding: Mapping[str, Any],
    cursor: Mapping[str, Any],
) -> bool:
    """Bind a recipe disposition to the report's preserved candidate."""

    raw_disposition = cursor.get("recipe_repair_disposition")
    if raw_disposition is None:
        return True
    if not isinstance(raw_disposition, Mapping):
        return False
    disposition = dict(raw_disposition)
    candidates = list(finding.get("candidates") or ())
    if len(candidates) != 1 or not isinstance(candidates[0], Mapping):
        return False
    candidate = dict(candidates[0])
    metadata = dict(candidate.get("metadata") or {})
    status = str(disposition.get("status") or "")
    expected_outcome = (
        "refuted" if status == "exhausted" else "transient_failure"
    )
    return bool(
        str(finding.get("engine") or "") == "function"
        and str(finding.get("outcome") or "") == expected_outcome
        and str(candidate.get("candidate_hash") or "")
        == str(disposition.get("candidate_hash") or "")
        and candidate == dict(disposition.get("candidate") or {})
        and metadata.get("right_pi_replay") is True
        and metadata.get("right_pi_plan_hash") == disposition.get("plan_hash")
        and metadata.get("right_pi_candidate_index")
        == disposition.get("candidate_index")
    )


def _merge_falsification_cursor(
    target_cursors: Dict[str, Any],
    *,
    engine: str,
    cursor: Any,
    mark_smt_resume_recheck: bool = False,
) -> bool:
    """Monotonically merge one validated engine cursor.

    Graph's old index-only cursor is unusable because graph resume requires
    the complete plan identity.  It may therefore be replaced by a fully
    identified cursor even at a lower index.  Index-only cursors for the
    ordinary deterministic engines remain usable and must never regress.
    """

    engine = str(engine or "").strip()
    candidate = _validated_falsification_cursor(cursor, engine=engine)
    if not engine or candidate is None:
        return False
    if (
        mark_smt_resume_recheck
        and engine == "sat_smt"
        and candidate.get("plan_hash")
    ):
        candidate["resume_recheck_due"] = True

    prior = _validated_falsification_cursor(
        target_cursors.get(engine),
        engine=engine,
    )
    if prior is None:
        target_cursors[engine] = candidate
        return True

    prior_index = int(prior["next_index"])
    candidate_index = int(candidate["next_index"])
    if engine == "graph":
        prior_is_resumable = all(
            prior.get(key) is not None
            for key in _GRAPH_CURSOR_REQUIRED_IDENTITY_KEYS
        )
        candidate_is_resumable = all(
            candidate.get(key) is not None
            for key in _GRAPH_CURSOR_REQUIRED_IDENTITY_KEYS
        )
        if candidate_is_resumable and not prior_is_resumable:
            target_cursors[engine] = candidate
            return True
        if prior_is_resumable and not candidate_is_resumable:
            return False
    if engine == "function":
        prior_is_right_pi = bool(
            prior.get("cursor_schema") == RIGHT_PI_PLAN_CURSOR_SCHEMA
            and prior.get("plan_hash")
        )
        candidate_is_right_pi = bool(
            candidate.get("cursor_schema") == RIGHT_PI_PLAN_CURSOR_SCHEMA
            and candidate.get("plan_hash")
        )
        if candidate_is_right_pi and not prior_is_right_pi:
            target_cursors[engine] = candidate
            return True
        if prior_is_right_pi and not candidate_is_right_pi:
            return False
        prior_recipe = prior.get("recipe_repair_disposition")
        candidate_recipe = candidate.get("recipe_repair_disposition")
        if (
            prior_is_right_pi
            and candidate_is_right_pi
            and prior_recipe is not None
            and candidate_recipe is None
            and candidate_index <= prior_index
            and prior.get("plan_hash") == candidate.get("plan_hash")
            and prior.get("domain_size") == candidate.get("domain_size")
        ):
            # A late watchdog report describes no progress beyond the parked
            # candidate.  It must not erase a bounded repair disposition and
            # reopen the identical full-negation recipe after branch merge or
            # checkpoint reconstruction.  Strict index progress (for example
            # a later successful certification) may still retire it.
            return False
        if (
            prior_is_right_pi
            and candidate_is_right_pi
            and prior_recipe is not None
            and candidate_recipe is not None
        ):
            prior_recipe_record = dict(prior_recipe)
            candidate_recipe_record = dict(candidate_recipe)
            if (
                prior_recipe_record.get("repair_key")
                == candidate_recipe_record.get("repair_key")
                and int(candidate_recipe_record.get("attempts") or 0)
                < int(prior_recipe_record.get("attempts") or 0)
            ):
                # Late branch/report arrival cannot reopen an identical
                # repair disposition after its durable bounded exhaustion.
                return False

    prior_has_identity = any(
        prior.get(key) is not None for key in _FALSIFICATION_CURSOR_IDENTITY_KEYS
    )
    candidate_has_identity = any(
        candidate.get(key) is not None
        for key in _FALSIFICATION_CURSOR_IDENTITY_KEYS
    )
    if prior_has_identity and not candidate_has_identity:
        return False
    if candidate_has_identity and not prior_has_identity:
        if engine == "sat_smt" and candidate.get("plan_hash") is not None:
            # Native SMT has exactly one plan-bound query and cannot resume
            # from an old index-only cursor (the Bool enumerator is the only
            # SAT/SMT mode where such a cursor has meaning).  Once a native
            # plan cursor arrives for this statement, upgrade it outright
            # just as graph upgrades its unusable legacy cursor.
            target_cursors[engine] = candidate
            return True
        candidate_domain_size = candidate.get("domain_size")
        prior_exceeds_candidate_domain = (
            candidate_domain_size is not None
            and prior_index > int(candidate_domain_size)
        )
        if candidate_index < prior_index and not prior_exceeds_candidate_domain:
            return False
        target_cursors[engine] = candidate
        return True

    incompatible = any(
        prior.get(key) != candidate.get(key)
        for key in _FALSIFICATION_CURSOR_IDENTITY_KEYS
        if prior.get(key) is not None or candidate.get(key) is not None
    )
    if incompatible:
        # Two complete but incompatible identities under one statement and
        # environment cannot be ordered safely.  The dossier cannot know
        # whether an old branch/report or the new report describes the live
        # engine plan, so fail closed: trust neither cursor.  The next engine
        # invocation starts at zero and can establish one identity from an
        # empty cache.  This also prevents a well-typed poisoned domain/plan
        # identity from pinning the corrected engine cursor forever.
        target_cursors.pop(engine, None)
        return False
    if candidate_index < prior_index:
        return False
    target_cursors[engine] = candidate
    return True


def _falsification_cursor_target_id(statement: str) -> str:
    exact = str(statement or "").strip()
    return hashlib.sha256(exact.encode("utf-8")).hexdigest() if exact else ""


def _falsification_cursor_target_entry(
    dossier: "ProofDossier",
    statement: str,
    *,
    falsification_environment_hash: str,
    create: bool,
) -> Optional[Dict[str, Any]]:
    """Resolve one exact cursor target inside a canonical shortlist.

    Historical checkpoints stored engines directly under a lossy canonical
    statement key.  Those entries have no exact owner and are intentionally
    not migrated as progress; the authenticated report ledger is rebuilt into
    this schema on resume, so dropping the denormalized legacy cache merely
    causes a safe recheck when no lineage exists.
    """

    exact = str(statement or "").strip()
    canonical = canonical_dossier_statement_key(exact)
    target_id = _falsification_cursor_target_id(exact)
    environment_hash = str(falsification_environment_hash or "").strip()
    if not canonical or not target_id:
        return None
    bucket = dossier.mini_falsification_cursors.get(canonical)
    if not (
        isinstance(bucket, dict)
        and bucket.get("__target_schema__") == FALSIFICATION_CURSOR_TARGET_SCHEMA
        and isinstance(bucket.get("__targets__"), dict)
    ):
        if not create:
            return None
        bucket = {
            "__target_schema__": FALSIFICATION_CURSOR_TARGET_SCHEMA,
            "__targets__": {},
        }
        dossier.mini_falsification_cursors[canonical] = bucket
    targets = bucket["__targets__"]
    entry = targets.get(target_id)
    valid_entry = bool(
        isinstance(entry, dict)
        and entry.get("__statement__") == exact
        and entry.get("__statement_hash__") == target_id
    )
    if not valid_entry:
        if not create:
            return None
        target_environment_hash = str(
            dossier.current_lean_environment_hash or ""
        ).strip()
        entry = {
            "__statement__": exact,
            "__statement_hash__": target_id,
            "__canonical_key__": canonical,
            "__target_environment_hash__": target_environment_hash,
            "__target_full_expr_hash__": _exact_statement_full_expr_hash(
                dossier,
                exact,
                target_environment_hash,
            ),
            "__environment_hash__": environment_hash,
        }
        targets[target_id] = entry
    elif create and entry.get("__environment_hash__") != environment_hash:
        # Falsification policy/helper/runtime changes define a fresh search
        # world.  Keep target identity but discard progress from the old one.
        target_environment_hash = str(
            dossier.current_lean_environment_hash or ""
        ).strip()
        entry = {
            "__statement__": exact,
            "__statement_hash__": target_id,
            "__canonical_key__": canonical,
            "__target_environment_hash__": target_environment_hash,
            "__target_full_expr_hash__": _exact_statement_full_expr_hash(
                dossier,
                exact,
                target_environment_hash,
            ),
            "__environment_hash__": environment_hash,
        }
        targets[target_id] = entry
    return entry


def _falsification_cursor_entries_for_statement(
    dossier: "ProofDossier",
    statement: str,
) -> tuple[Dict[str, Any], ...]:
    """Return an exact target, or bound full-expr aliases from its shortlist."""

    exact = str(statement or "").strip()
    canonical = canonical_dossier_statement_key(exact)
    target_id = _falsification_cursor_target_id(exact)
    bucket = dossier.mini_falsification_cursors.get(canonical)
    if not (
        canonical
        and isinstance(bucket, dict)
        and bucket.get("__target_schema__") == FALSIFICATION_CURSOR_TARGET_SCHEMA
        and isinstance(bucket.get("__targets__"), dict)
    ):
        return ()
    targets = bucket["__targets__"]
    exact_entry = targets.get(target_id)
    if (
        isinstance(exact_entry, dict)
        and exact_entry.get("__statement__") == exact
        and exact_entry.get("__statement_hash__") == target_id
    ):
        return (exact_entry,)

    target_environment_hash = str(
        dossier.current_lean_environment_hash or ""
    ).strip()
    target_full_expr_hash = _exact_statement_full_expr_hash(
        dossier,
        exact,
        target_environment_hash,
    )
    if not target_environment_hash or not target_full_expr_hash:
        return ()
    return tuple(
        entry
        for entry in targets.values()
        if isinstance(entry, dict)
        and entry.get("__canonical_key__") == canonical
        and entry.get("__target_environment_hash__")
        == target_environment_hash
        and entry.get("__target_full_expr_hash__") == target_full_expr_hash
    )


def _falsification_report_has_unpromoted_candidate(
    report: Mapping[str, Any],
) -> bool:
    return any(
        isinstance(finding, Mapping)
        and bool(list(finding.get("candidates") or ()))
        and not (
            isinstance(finding.get("certificate"), Mapping)
            and bool(finding["certificate"].get("authoritative"))
        )
        for finding in report.get("findings") or ()
    )


def _falsification_report_affects_advisory_quarantine(
    report: Mapping[str, Any],
) -> bool:
    """Whether a report can establish or clear an advisory candidate.

    A watchdog/backend failure and an unsupported engine establish no new
    mathematical evidence, so neither may erase an earlier durable witness.
    Candidate-bearing reports establish quarantine; completed inconclusive or
    verified-true reports may clear it.
    """

    if _falsification_report_has_unpromoted_candidate(report):
        return True
    evidence_outcome = str(report.get("evidence_outcome") or "")
    if not evidence_outcome:
        finding_outcomes = {
            str(finding.get("outcome") or "")
            for finding in report.get("findings") or ()
            if isinstance(finding, Mapping)
        }
        if "refuted" in finding_outcomes:
            evidence_outcome = "refuted"
        elif "transient_failure" in finding_outcomes:
            evidence_outcome = "transient_failure"
        elif "inconclusive" in finding_outcomes:
            evidence_outcome = "inconclusive"
        elif "verified_true" in finding_outcomes:
            evidence_outcome = "verified_true"
        else:
            evidence_outcome = "unsupported"
    return evidence_outcome in {"inconclusive", "verified_true"}


def _falsification_report_evidence_order_key(
    report: Mapping[str, Any],
) -> Tuple[float, int, str]:
    """Content-authenticated recency with conservative equal-time ordering.

    Wall-clock timestamps can collide across concurrent branches. At an equal
    evidence time, a report with no advisory candidate must outrank a stale
    candidate report: a content hash is deterministic but carries no causal
    meaning and therefore cannot safely decide whether quarantine was cleared.
    """

    from .mini_falsification import falsification_report_record_is_valid

    if not falsification_report_record_is_valid(report):
        return (-1.0, -1, "")
    has_unpromoted_candidate = (
        _falsification_report_has_unpromoted_candidate(report)
    )
    return (
        float(report.get("started_at") or 0.0),
        0 if has_unpromoted_candidate else 1,
        str(report.get("report_hash") or ""),
    )


def _sort_falsification_ledger_by_evidence_time(
    reports: List[Dict[str, Any]],
) -> None:
    """Keep branch propagation order from masquerading as evidence recency."""

    reports.sort(key=_falsification_report_evidence_order_key)


def _latest_helper_falsification_report_for_key(
    reports: Sequence[Mapping[str, Any]],
    statement_key: str,
) -> Optional[Mapping[str, Any]]:
    """Latest validated helper report independent of list/merge ordering."""

    from .mini_falsification import falsification_report_record_is_valid

    applicable = [
        report
        for report in reports
        if falsification_report_record_is_valid(report)
        and canonical_dossier_statement_key(
            str(report.get("statement") or "")
        )
        == statement_key
        and str(report.get("target_kind") or "") == "helper"
        and _falsification_report_affects_advisory_quarantine(report)
    ]
    if not applicable:
        return None
    return max(applicable, key=_falsification_report_evidence_order_key)


def propagate_invalidated_statements(
    parent: "ProofDossier",
    child: "ProofDossier",
    *,
    record_graph: bool = True,
) -> int:
    """Carry child mini-recursive claim tombstones without carrying proposals."""

    from .mini_falsification import (
        authoritative_certificate_record_is_valid,
        falsification_report_record_is_valid,
    )
    from .mini_falsification.model import (
        FalsificationReport,
        TargetKind,
        content_hash,
        finding_from_record,
    )

    if parent is child:
        return 0
    parent_root_statement = _exact_statement_text(parent.root_statement)
    parent_target_environment_hash = str(
        parent.current_lean_environment_hash or ""
    ).strip()
    normalized_reports: List[Dict[str, Any]] = []
    report_hash_remap: Dict[str, str] = {}
    normalized_report_by_original_hash: Dict[str, Dict[str, Any]] = {}
    for raw_report in getattr(child, "mini_falsification_ledger", []) or []:
        if not isinstance(raw_report, dict):
            continue
        if not falsification_report_record_is_valid(raw_report):
            continue
        original_hash = str(raw_report.get("report_hash") or "")
        report = copy.deepcopy(raw_report)
        if (
            str(report.get("target_kind") or "") == "root"
            and not _statements_share_bound_lean_identity(
                parent,
                _exact_statement_text(report.get("statement")),
                parent_root_statement,
                str(parent.current_lean_environment_hash or "").strip(),
            )
        ):
            # ``root`` is dossier-relative.  Once a recursive child's root
            # report crosses into its parent it is helper evidence, never a
            # claim about the parent's root.  Re-envelope the immutable report
            # so checkpoint replay preserves that scope without conferring
            # root authority or tripping the parent's root-linkage guard.
            report["target_kind"] = "helper"
            report.pop("report_hash", None)
            report["report_hash"] = content_hash(report)
        if not falsification_report_record_is_valid(report):
            continue
        report_hash = str(report.get("report_hash") or "")
        report_hash_remap[original_hash] = report_hash
        normalized_report_by_original_hash[original_hash] = report
        normalized_reports.append(report)
    copied = 0
    quarantined_certificate_hashes = {
        str(dict(item.get("certificate") or {}).get("certificate_hash") or "")
        for item in getattr(parent, "mini_falsification_pending_certificates", [])
        or []
        if isinstance(item, dict)
    }

    def preserve_quarantined_report(report: Mapping[str, Any]) -> None:
        """Keep transportable evidence without manufacturing parent authority."""

        report_hash = str(report.get("report_hash") or "")
        if report_hash and not any(
            str(item.get("report_hash") or "") == report_hash
            for item in parent.mini_falsification_ledger
            if isinstance(item, Mapping)
        ):
            parent.mini_falsification_ledger.append(copy.deepcopy(dict(report)))
            _sort_falsification_ledger_by_evidence_time(
                parent.mini_falsification_ledger
            )
        for finding in list(report.get("findings") or ()):
            if not isinstance(finding, Mapping):
                continue
            certificate = finding.get("certificate")
            if not isinstance(certificate, Mapping):
                continue
            certificate_record = dict(certificate)
            certificate_hash = str(
                certificate_record.get("certificate_hash") or ""
            ).strip()
            if (
                not certificate_hash
                or certificate_hash in quarantined_certificate_hashes
                or not bool(certificate_record.get("authoritative"))
                or not authoritative_certificate_record_is_valid(
                    certificate_record
                )
            ):
                continue
            parent.mini_falsification_pending_certificates.append(
                {
                    "certificate": copy.deepcopy(certificate_record),
                    "report_hash": report_hash,
                    "target_kind": str(
                        report.get("target_kind") or "helper"
                    ),
                    # This is the source authority's target environment.  It
                    # is audit linkage only: FalsifyTargetAction must replay
                    # the proof in the parent's live environment before the
                    # certificate can become authority there.
                    "target_environment_hash": next(
                        (
                            str(authority.get("target_environment_hash") or "")
                            .strip()
                            for authority in child.mini_authoritative_negations.values()
                            if isinstance(authority, Mapping)
                            and str(authority.get("certificate_hash") or "").strip()
                            == certificate_hash
                        ),
                        "",
                    ),
                }
            )
            quarantined_certificate_hashes.add(certificate_hash)

    # All child evidence crosses the same parent admission boundary as a local
    # report. Never copy an invalidation reason/provenance tuple independently
    # of its complete content-addressed report and certificate.
    for report in normalized_reports:
        certificate_hashes = {
            str(dict(item.get("certificate") or {}).get("certificate_hash") or "")
            for item in report.get("findings") or ()
            if isinstance(item, Mapping)
            and isinstance(item.get("certificate"), Mapping)
            and bool(dict(item.get("certificate") or {}).get("authoritative"))
        }
        child_live_certificate_hashes = {
            str(authority.get("certificate_hash") or "")
            for authority in child.mini_authoritative_negations.values()
            if isinstance(authority, Mapping)
        }
        child_same_environment_certificate_hashes = {
            str(authority.get("certificate_hash") or "")
            for authority in child.mini_authoritative_negations.values()
            if isinstance(authority, Mapping)
            and str(authority.get("target_environment_hash") or "").strip()
            == parent_target_environment_hash
        }
        if certificate_hashes and (
            not certificate_hashes.intersection(child_live_certificate_hashes)
            or not parent_target_environment_hash
            or not certificate_hashes.issubset(
                child_same_environment_certificate_hashes
            )
        ):
            # A restored child carries report history and a quarantined replay
            # candidate, not live Lean authority. A still-live child from a
            # different target environment has the same status: its theorem
            # proof may be replayable, but it cannot be re-minted under the
            # parent's environment stamp by object transport alone.
            preserve_quarantined_report(report)
            continue
        reconstructed = FalsificationReport(
            statement=str(report.get("statement") or ""),
            target_kind=TargetKind(str(report.get("target_kind") or "helper")),
            findings=tuple(
                finding_from_record(item)
                for item in report.get("findings") or ()
                if isinstance(item, Mapping)
            ),
            started_at=float(report.get("started_at") or 0.0),
            policy_hash=str(report.get("policy_hash") or ""),
            environment_hash=str(report.get("environment_hash") or ""),
        )
        if reconstructed.to_record() != report:
            # Reconstruction is the type boundary. Any field that cannot make
            # the round trip is not silently granted authority.
            continue
        already_active = any(
            str(authority.get("certificate_hash") or "") in certificate_hashes
            for authority in parent.mini_authoritative_negations.values()
            if isinstance(authority, Mapping)
        )
        promoted = parent.record_falsification_report(reconstructed)
        copied += int(promoted and not already_active)
    known_pending_hashes = {
        str(dict(item.get("certificate") or {}).get("certificate_hash") or "")
        for item in getattr(parent, "mini_falsification_pending_certificates", [])
        or []
        if isinstance(item, dict)
    }
    child_reports_by_hash = {
        str(item.get("report_hash") or ""): item
        for item in getattr(child, "mini_falsification_ledger", []) or []
        if isinstance(item, dict) and falsification_report_record_is_valid(item)
    }
    for item in getattr(child, "mini_falsification_pending_certificates", []) or []:
        if not isinstance(item, dict) or not isinstance(item.get("certificate"), dict):
            continue
        source_report_hash = str(item.get("report_hash") or "")
        source_report = child_reports_by_hash.get(source_report_hash)
        normalized_report = normalized_report_by_original_hash.get(
            source_report_hash
        )
        certificate_hash = str(
            item["certificate"].get("certificate_hash") or ""
        )
        if (
            certificate_hash
            and certificate_hash not in known_pending_hashes
            and authoritative_certificate_record_is_valid(item["certificate"])
            and source_report is not None
            and normalized_report is not None
            and any(
                isinstance(finding, dict)
                and isinstance(finding.get("certificate"), dict)
                and str(finding["certificate"].get("certificate_hash") or "")
                == certificate_hash
                for finding in source_report.get("findings") or ()
            )
        ):
            normalized_pending = copy.deepcopy(item)
            normalized_pending["report_hash"] = str(
                normalized_report.get("report_hash") or ""
            )
            normalized_pending["target_kind"] = str(
                normalized_report.get("target_kind") or "helper"
            )
            parent.mini_falsification_pending_certificates.append(
                normalized_pending
            )
            known_pending_hashes.add(certificate_hash)
    normalized_certificate_hashes = {
        str(certificate.get("certificate_hash") or "")
        for report in normalized_reports
        for finding in report.get("findings") or ()
        if isinstance(finding, dict)
        for certificate in [finding.get("certificate")]
        if isinstance(certificate, dict)
    }
    for disposition_id, disposition in dict(
        getattr(
            child,
            "mini_falsification_certificate_replay_dispositions",
            {},
        )
        or {}
    ).items():
        if not _certificate_replay_disposition_is_valid(disposition):
            continue
        certificate_hash = str(disposition.get("certificate_hash") or "")
        expected_id = _certificate_replay_disposition_id(
            certificate_hash,
            str(disposition.get("environment_hash") or ""),
            str(disposition.get("policy_hash") or ""),
        )
        if (
            str(disposition_id or "") != expected_id
            or certificate_hash not in normalized_certificate_hashes
        ):
            continue
        parent.mini_falsification_certificate_replay_dispositions[
            expected_id
        ] = copy.deepcopy(disposition)
    # Cursor admission already happened through ``record_falsification_report``
    # above. A second direct merge would bypass its incompatible-plan
    # fail-closed semantics.
    if copied and record_graph:
        parent.record_graph_event(
            {
                "phase": "mini_recursive_claim_invalidated",
                "helper_name": "validated_child_falsification_reports",
                "statement": "",
                "invalid_reason": "complete child report admitted by parent",
                "verdict": "claim_skipped_previous_child_invalidation",
            }
        )
    return copied


def _purge_proposed_helpers_for_statement_key(
    dossier: "ProofDossier",
    statement_key: str,
    reason: str = "",
    *,
    target_environment_hash: str = "",
) -> None:
    key = str(statement_key or "").strip()
    if not key:
        return
    authority_environment_hash = str(target_environment_hash or "").strip()
    if authority_environment_hash:
        authority_statements = _authoritative_invalidation_statement_texts(
            dossier, key, authority_environment_hash
        )
        for name, item in list(getattr(dossier, "proposed_helpers", {}).items()):
            if (
                _exact_statement_text(getattr(item, "statement", ""))
                in authority_statements
                and str(
                    getattr(item, "statement_environment_hash", "") or ""
                ).strip()
                == authority_environment_hash
            ):
                dossier.proposed_helpers.pop(name, None)
    # Legacy unstamped proposals deliberately survive stamped authority.
    _reject_graph_native_proposals_for_statement_key(
        dossier,
        key,
        reason=reason,
        target_environment_hash=target_environment_hash,
    )


_INVALIDATED_PARENT_STATEMENT_FIELDS = (
    "materialization_parent_statement",
    "formalization_bridge_parent_statement",
    "formalization_rejected_bridge_parent_statement",
    "parent_repair_target_statement",
)


def _exact_statement_text(statement: Any) -> str:
    """Return the certificate identity carried across process boundaries.

    Canonical statement keys are deliberately *not* proof identity.  They are
    lossy search indexes and can collapse distinct binder structures.
    """

    return str(statement or "").strip()


def _authoritative_negation_id(record: Mapping[str, Any]) -> str:
    payload = {
        "statement": _exact_statement_text(record.get("statement")),
        "target_environment_hash": str(
            record.get("target_environment_hash") or ""
        ).strip(),
        "target_full_expr_hash": str(
            record.get("target_full_expr_hash") or ""
        ).strip(),
        "certificate_hash": str(record.get("certificate_hash") or "").strip(),
        "report_hash": str(record.get("report_hash") or "").strip(),
    }
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def _exact_statement_full_expr_hash(
    dossier: "ProofDossier",
    statement: str,
    target_environment_hash: str,
) -> str:
    """Return one receipt-bound identity for this exact surface statement."""

    graph = getattr(dossier, "proof_graph", None)
    exact = _exact_statement_text(statement)
    environment_hash = str(target_environment_hash or "").strip()
    if graph is None or not exact or not environment_hash:
        return ""
    hashes: Set[str] = set()
    for node in list(getattr(graph, "nodes", {}).values()):
        if _exact_statement_text(getattr(node, "statement", "")) != exact:
            continue
        if str(
            (getattr(node, "metadata", {}) or {}).get(
                "statement_environment_hash"
            )
            or ""
        ).strip() != environment_hash:
            continue
        parsed = parse_lean_contract_identity(
            graph_node_bound_contract_identity(node)
        )
        if parsed is not None:
            hashes.add(parsed[0])
    return next(iter(hashes)) if len(hashes) == 1 else ""


def _statements_share_bound_lean_identity(
    dossier: "ProofDossier",
    left: str,
    right: str,
    target_environment_hash: str,
) -> bool:
    """Compare exact bytes or two receipts from the same Lean environment."""

    left_exact = _exact_statement_text(left)
    right_exact = _exact_statement_text(right)
    if left_exact == right_exact:
        return bool(left_exact)
    environment_hash = str(target_environment_hash or "").strip()
    if not environment_hash:
        return False
    left_hash = _exact_statement_full_expr_hash(
        dossier, left_exact, environment_hash
    )
    right_hash = _exact_statement_full_expr_hash(
        dossier, right_exact, environment_hash
    )
    return bool(left_hash and right_hash and left_hash == right_hash)


def _active_authorities_for_key(
    dossier: "ProofDossier",
    statement_key: str,
    target_environment_hash: str,
) -> List[Dict[str, Any]]:
    key = str(statement_key or "").strip()
    environment_hash = str(target_environment_hash or "").strip()
    return [
        dict(item)
        for item in dict(
            getattr(dossier, "mini_authoritative_negations", {}) or {}
        ).values()
        if isinstance(item, Mapping)
        and canonical_dossier_statement_key(item.get("statement") or "") == key
        and str(item.get("target_environment_hash") or "").strip()
        == environment_hash
    ]


def _verified_helpers_conflicting_with_falsification(
    dossier: Any,
    statement: str,
    target_environment_hash: str,
    *,
    target_full_expr_hash: str = "",
) -> List[str]:
    """Return verified helpers that prove the statement being falsified."""

    exact_statement = _exact_statement_text(statement)
    environment_hash = str(target_environment_hash or "").strip()
    full_expr_hash = str(target_full_expr_hash or "").strip()
    if not full_expr_hash:
        full_expr_hash = _exact_statement_full_expr_hash(
            dossier,
            exact_statement,
            environment_hash,
        )
    conflicts: List[str] = []
    for name, helper in dict(
        getattr(dossier, "verified_helpers", {}) or {}
    ).items():
        helper_statement = _exact_statement_text(
            helper_decl_statement(getattr(helper, "source", "") or "")
        )
        helper_identity = parse_lean_contract_identity(
            verified_helper_bound_contract_identity(helper)
        )
        helper_environment_hash = str(
            getattr(helper, "verification_environment_hash", "") or ""
        ).strip()
        if helper_statement == exact_statement or bool(
            full_expr_hash
            and helper_identity is not None
            and helper_identity[0] == full_expr_hash
            and helper_environment_hash == environment_hash
        ):
            conflicts.append(str(name or ""))
    return conflicts


def _record_falsification_trust_boundary_conflict(
    dossier: Any,
    *,
    certificate_hash: str,
) -> None:
    clean_hash = str(certificate_hash or "").strip()
    durable_hashes = (
        dossier.mini_falsification_trust_boundary_conflict_certificate_hashes
    )
    if clean_hash and clean_hash not in durable_hashes:
        dossier.increment_tool_metric(
            "mini_falsification_trust_boundary_conflicts",
            1,
        )
        durable_hashes.add(clean_hash)
    receipts = getattr(
        dossier,
        "_mini_falsification_trust_boundary_conflict_certificate_hashes",
        None,
    )
    if not isinstance(receipts, set):
        receipts = set()
        setattr(
            dossier,
            "_mini_falsification_trust_boundary_conflict_certificate_hashes",
            receipts,
        )
    if clean_hash:
        receipts.add(clean_hash)


def active_root_disproof_certificate_is_valid(
    dossier: Any,
    *,
    reject_proof_conflicts: bool = True,
) -> bool:
    """Validate that the dossier owns live authority for its root disproof."""

    from .mini_falsification import (
        authoritative_certificate_record_is_valid,
        falsification_report_record_is_valid,
    )

    certificate = getattr(dossier, "root_disproof_certificate", None)
    if not authoritative_certificate_record_is_valid(certificate):
        return False
    certificate_hash = str(certificate.get("certificate_hash") or "").strip()
    if (
        str(getattr(dossier, "session_failure_reason", "") or "").strip()
        == "falsification_trust_boundary_conflict"
        and str(getattr(dossier, "session_failure_kind", "") or "").strip()
        == "proof_disproof_conflict"
        and certificate_hash
        in set(
            getattr(
                dossier,
                "mini_falsification_trust_boundary_conflict_certificate_hashes",
                set(),
            )
            or ()
        )
        and certificate_hash
        in set(
            getattr(
                dossier,
                "_mini_falsification_trust_boundary_conflict_certificate_hashes",
                set(),
            )
            or ()
        )
    ):
        return False
    current_environment_hash = str(
        getattr(dossier, "current_lean_environment_hash", "") or ""
    ).strip()
    root_statement = _exact_statement_text(
        getattr(dossier, "root_statement", "")
    )
    if not certificate_hash or not current_environment_hash or not root_statement:
        return False
    if any(
        isinstance(item, Mapping)
        and isinstance(item.get("certificate"), Mapping)
        and str(
            dict(item.get("certificate") or {}).get("certificate_hash") or ""
        ).strip()
        == certificate_hash
        for item in (
            getattr(dossier, "mini_falsification_pending_certificates", []) or []
        )
    ):
        return False

    validated_reports: Dict[str, Mapping[str, Any]] = {}
    for report in getattr(dossier, "mini_falsification_ledger", []) or []:
        if (
            not isinstance(report, Mapping)
            or not falsification_report_record_is_valid(report)
            or str(report.get("target_kind") or "") != "root"
        ):
            continue
        report_statement = _exact_statement_text(report.get("statement"))
        if not _statements_share_bound_lean_identity(
            dossier,
            report_statement,
            root_statement,
            current_environment_hash,
        ):
            continue
        if (
            _exact_statement_text(certificate.get("statement"))
            != report_statement
            or str(certificate.get("environment_hash") or "").strip()
            != str(report.get("environment_hash") or "").strip()
        ):
            continue
        if not any(
            isinstance(finding, Mapping)
            and isinstance(finding.get("certificate"), Mapping)
            and str(
                finding["certificate"].get("certificate_hash") or ""
            ).strip()
            == certificate_hash
            and authoritative_certificate_record_is_valid(
                finding["certificate"]
            )
            for finding in report.get("findings") or ()
        ):
            continue
        report_hash = str(report.get("report_hash") or "").strip()
        if report_hash:
            validated_reports[report_hash] = report
    if not validated_reports:
        return False

    for authority_id, authority in dict(
        getattr(dossier, "mini_authoritative_negations", {}) or {}
    ).items():
        if not isinstance(authority, Mapping):
            continue
        authority_key = str(authority_id or "").strip()
        if (
            not authority_key
            or authority_key != _authoritative_negation_id(authority)
            or str(authority.get("authority_id") or "").strip() != authority_key
            or str(authority.get("certificate_hash") or "").strip()
            != certificate_hash
            or str(authority.get("report_hash") or "").strip()
            not in validated_reports
            or str(authority.get("target_environment_hash") or "").strip()
            != current_environment_hash
        ):
            continue
        if _statements_share_bound_lean_identity(
            dossier,
            _exact_statement_text(authority.get("statement")),
            root_statement,
            current_environment_hash,
        ):
            if reject_proof_conflicts and (
                bool(getattr(dossier, "final_proof", None))
                or bool(getattr(dossier, "final_proof_hash", None))
                or bool(
                    _verified_helpers_conflicting_with_falsification(
                        dossier,
                        _exact_statement_text(certificate.get("statement")),
                        current_environment_hash,
                        target_full_expr_hash=str(
                            authority.get("target_full_expr_hash") or ""
                        ),
                    )
                )
            ):
                return False
            return True
    return False


def _node_references_invalidated_parent(
    node: Any,
    statement_key: str,
    *,
    authority_statements: Optional[Set[str]] = None,
) -> bool:
    """Whether graph work was manufactured solely to support this target."""

    metadata = dict(getattr(node, "metadata", {}) or {})
    exact_statements = {
        _exact_statement_text(item) for item in (authority_statements or set()) if item
    }
    if exact_statements:
        return any(
            _exact_statement_text(metadata.get(field)) in exact_statements
            for field in _INVALIDATED_PARENT_STATEMENT_FIELDS
        )
    # No live authority means a canonical key is only advisory.
    return False


def _authoritative_invalidation_full_expr_hashes(
    dossier: "ProofDossier",
    statement_key: str,
    target_environment_hash: str,
) -> Set[str]:
    """Collect receipt-bound Lean identities for exact target occurrences."""

    key = str(statement_key or "").strip()
    environment_hash = str(target_environment_hash or "").strip()
    if not key or not environment_hash:
        return set()
    return {
        str(item.get("target_full_expr_hash") or "").strip()
        for item in _active_authorities_for_key(dossier, key, environment_hash)
        if str(item.get("target_full_expr_hash") or "").strip()
    }


def _authoritative_invalidation_statement_texts(
    dossier: "ProofDossier",
    statement_key: str,
    target_environment_hash: str,
) -> Set[str]:
    return {
        _exact_statement_text(item.get("statement"))
        for item in _active_authorities_for_key(
            dossier, statement_key, target_environment_hash
        )
        if _exact_statement_text(item.get("statement"))
    }


def _node_matches_authoritative_invalidation(
    node: Any,
    *,
    statement_key: str,
    target_environment_hash: str,
    full_expr_hashes: Set[str],
    authority_statements: Set[str],
) -> bool:
    """Match exact surface aliases or receipt-bound elaborated aliases."""

    environment_hash = str(target_environment_hash or "").strip()
    if str(
        (getattr(node, "metadata", {}) or {}).get("statement_environment_hash")
        or ""
    ).strip() != environment_hash:
        return False
    if _exact_statement_text(getattr(node, "statement", "")) in authority_statements:
        return True
    parsed = parse_lean_contract_identity(graph_node_bound_contract_identity(node))
    return bool(parsed is not None and parsed[0] in full_expr_hashes)


def _authority_ids_matching_node(
    dossier: "ProofDossier",
    node: Any,
    statement_key: str,
    target_environment_hash: str,
) -> Set[str]:
    matches: Set[str] = set()
    parsed = parse_lean_contract_identity(graph_node_bound_contract_identity(node))
    node_full_expr_hash = parsed[0] if parsed is not None else ""
    node_statement = _exact_statement_text(getattr(node, "statement", ""))
    for authority in _active_authorities_for_key(
        dossier, statement_key, target_environment_hash
    ):
        if node_statement == _exact_statement_text(authority.get("statement")) or bool(
            node_full_expr_hash
            and node_full_expr_hash
            == str(authority.get("target_full_expr_hash") or "").strip()
        ):
            authority_id = str(authority.get("authority_id") or "").strip()
            if authority_id:
                matches.add(authority_id)
    return matches


def _preserve_authoritative_reformulation_candidates(
    dossier: "ProofDossier",
    statement_key: str,
    *,
    reason: str,
    target_environment_hash: str,
) -> List[str]:
    """Re-home executable alternatives before their false-parent route retires.

    Formalization turns often discover the corrected proposition while trying
    to repair a bad parent formulation.  The candidate is not a fact, but it is
    valuable proof-idea memory.  Clone it into a fresh route with no dependency
    on the falsified parent.  Natural-language bridge briefs are deliberately
    excluded: only a syntactically executable Lean proposition can become new
    proof work.
    """

    graph = getattr(dossier, "proof_graph", None)
    key = str(statement_key or "").strip()
    environment_hash = str(target_environment_hash or "").strip()
    if graph is None or not key or not environment_hash:
        return []
    authority_statements = _authoritative_invalidation_statement_texts(
        dossier, key, environment_hash
    )
    existing_node_ids = set(getattr(graph, "nodes", {}))
    candidate_sources: List[Tuple[Any, str]] = []
    for node in list(getattr(graph, "nodes", {}).values()):
        if not _node_references_invalidated_parent(
            node, key, authority_statements=authority_statements
        ):
            continue
        node_metadata = dict(getattr(node, "metadata", {}) or {})
        own_statement = str(getattr(node, "statement", "") or "").strip()
        if (
            own_statement
            and canonical_dossier_statement_key(own_statement) != key
            and graph_statement_is_executable(own_statement)
            and str(
                node_metadata.get("formalization_rejected_bridge_reason") or ""
            ).strip()
            == "formalization_helper_replay_failed"
        ):
            candidate_sources.append((node, own_statement))
    preserved: List[str] = []
    seen_keys: Set[str] = set()
    for source_node, statement in candidate_sources:
        candidate_key = canonical_dossier_statement_key(statement)
        if not candidate_key or candidate_key in seen_keys:
            continue
        seen_keys.add(candidate_key)
        source_metadata = dict(getattr(source_node, "metadata", {}) or {})
        source_route_id = str(
            source_metadata.get("route_id")
            or source_metadata.get("formalization_rejected_bridge_route_id")
            or ""
        ).strip()
        route_key = stable_identity(
            "authoritative-reformulation-route",
            key,
            candidate_key,
            environment_hash,
        )
        route = graph.record_strategy_route(
            name=f"reformulate_{text_hash(candidate_key)}",
            description=(
                "Re-evaluate an executable alternative formulation preserved "
                "after Lean certified that its former parent target is false."
            ),
            route_key=route_key,
            score=0.8,
            phase="authoritative_falsification",
            turn_index=int(getattr(source_node, "turn_index", 0) or 0),
            metadata={
                "route_scope": "partial_route",
                "source": "authoritative_target_reformulation",
                "authoritative_reformulation_candidate": True,
                "reformulates_invalidated_statement_key": key,
                "source_route_id": source_route_id,
                "source_graph_node_id": str(
                    getattr(source_node, "node_id", "") or ""
                ),
                "statement_environment_hash": environment_hash,
            },
        )
        claim = graph.record_proposed_claim(
            name=f"reformulation_{text_hash(candidate_key)}",
            statement=statement,
            claim_key=stable_identity(
                "authoritative-reformulation-claim",
                key,
                candidate_key,
                environment_hash,
            ),
            phase="authoritative_falsification",
            turn_index=int(getattr(source_node, "turn_index", 0) or 0),
            metadata={
                "source": "authoritative_target_reformulation",
                "authoritative_reformulation_candidate": True,
                "reformulates_invalidated_statement_key": key,
                "source_graph_node_id": str(
                    getattr(source_node, "node_id", "") or ""
                ),
                "statement_environment_hash": environment_hash,
                "formalization_required": False,
                "proof_authority": False,
            },
        )
        graph.attach_claim_to_route(route.node_id, claim.node_id)

        route_parents = [
            idea
            for idea in dossier.proof_ideas.values()
            if source_route_id and source_route_id in idea.consumer_ids
        ]
        if len(route_parents) == 1:
            parent_idea = route_parents[0]
        elif route_parents:
            # A route claimed by multiple lifecycle objects is ambiguous
            # durable state.  Preserve the reformulation without inventing a
            # parent edge.
            parent_idea = None
        else:
            statement_parents = [
                idea
                for idea in dossier.proof_ideas.values()
                if any(
                    canonical_dossier_statement_key(intent.statement) == key
                    for intent in idea.claim_intents
                )
            ]
            parent_idea = (
                statement_parents[0] if len(statement_parents) == 1 else None
            )
        root_identity = (
            parent_idea.root_statement_identity
            if parent_idea is not None
            else structural_statement_identity(
                dossier.root_statement,
                statement_key=canonical_dossier_statement_key(
                    dossier.root_statement
                ),
            )
        )
        strategy = (
            "Reformulate a Lean-falsified claim through the preserved "
            f"executable candidate: {statement}"
        )
        idea_id = proof_idea_identity(
            theorem_name=dossier.theorem_name,
            root_statement_identity=root_identity,
            strategy=strategy,
        )
        branch_id = stable_identity(
            "proof-idea-reformulation-branch",
            idea_id,
            route.node_id,
        )
        envelope = ProofLineageEnvelope(
            proof_idea_id=idea_id,
            route_id=route.node_id,
            claim_id=claim.node_id,
            statement_identity=structural_statement_identity(
                statement,
                statement_key=candidate_key,
            ),
        )
        route.metadata.update(envelope.merged_metadata(route.metadata))
        claim.metadata.update(envelope.merged_metadata(claim.metadata))
        route.metadata["branch_id"] = branch_id
        claim.metadata["branch_id"] = branch_id
        dossier.upsert_proof_idea(
            ProofIdeaRecord(
                theorem_name=dossier.theorem_name,
                root_statement_identity=root_identity,
                strategy=strategy,
                parent_proof_idea_id=(
                    parent_idea.proof_idea_id if parent_idea is not None else ""
                ),
                status_history=(
                    ProofIdeaStatusTransition.create(
                        proof_idea_id=idea_id,
                        occurrence_key=route.node_id,
                        status="active",
                        authority="controller",
                        reason=(
                            "executable alternative detached from a "
                            "Lean-falsified parent formulation"
                        ),
                        turn_index=int(
                            getattr(source_node, "turn_index", 0) or 0
                        ),
                        route_id=route.node_id,
                        branch_id=branch_id,
                    ),
                ),
                branch_provenance=(
                    ProofIdeaBranchProvenance(
                        branch_id=branch_id,
                        source="authoritative_target_reformulation",
                    ),
                ),
                consumer_ids=(route.node_id,),
                claim_intents=(
                    ProofIdeaClaimIntent(
                        claim_id=claim.node_id,
                        statement_identity=envelope.statement_identity,
                        statement=statement,
                        rationale=(
                            "independently validate the corrected formulation; "
                            "it is not support for the falsified parent"
                        ),
                        consumer_ids=(route.node_id,),
                    ),
                ),
                notes=(
                    str(reason or "authoritative parent invalidation"),
                    "candidate remains unproved until Lean accepts it",
                ),
            )
        )
        if claim.node_id not in existing_node_ids:
            preserved.append(claim.node_id)
            existing_node_ids.add(claim.node_id)
    if preserved:
        dossier.increment_tool_metric(
            "mini_authoritative_reformulation_candidates_preserved",
            len(preserved),
        )
    return preserved


def _record_authoritative_proof_idea_claim_invalidations(
    dossier: "ProofDossier",
    statement_key: str,
    *,
    reason: str,
    target_environment_hash: str,
    provenance: Optional[Mapping[str, Any]],
) -> int:
    """Project Lean refutation authority into claim-scoped idea lifecycle.

    A certificate invalidates a proposition, not every mathematical strategy
    that once mentioned it.  Record a Lean-authoritative *claim* resolution and
    retain alternative formulations in the aggregate.  Route retirement stays
    graph-authoritative; the conserved idea now explains exactly which
    formulation failed and why a reformulation route was created.
    """

    key = str(statement_key or "").strip()
    environment_hash = str(target_environment_hash or "").strip()
    if not key or not environment_hash:
        return 0
    provenance_record = dict(provenance or {})
    certificate = provenance_record.get("certificate")
    certificate_record = dict(certificate or {}) if isinstance(certificate, Mapping) else {}
    evidence_id = str(
        certificate_record.get("certificate_hash")
        or provenance_record.get("certificate_hash")
        or provenance_record.get("source_hash")
        or provenance_record.get("proof_hash")
        or provenance_record.get("report_hash")
        or ""
    ).strip()
    if not evidence_id:
        return 0
    graph = getattr(dossier, "proof_graph", None)
    full_expr_hashes = _authoritative_invalidation_full_expr_hashes(
        dossier,
        key,
        environment_hash,
    )
    authority_statements = _authoritative_invalidation_statement_texts(
        dossier, key, environment_hash
    )
    matching_node_ids = tuple(
        sorted(
            node.node_id
            for node in list(getattr(graph, "nodes", {}).values())
            if _node_matches_authoritative_invalidation(
                node,
                statement_key=key,
                target_environment_hash=environment_hash,
                full_expr_hashes=full_expr_hashes,
                authority_statements=authority_statements,
            )
        )
    )
    matching_claim_coordinates = {
        coordinate
        for node_id in matching_node_ids
        for coordinate in (
            node_id,
            str(
                (
                    getattr(graph.nodes.get(node_id), "metadata", {})
                    if graph is not None and graph.nodes.get(node_id) is not None
                    else {}
                ).get("claim_id")
                or ""
            ).strip(),
        )
        if coordinate
    }
    added = 0
    for idea_id, idea in list(dossier.proof_ideas.items()):
        matching_intents = [
            intent
            for intent in idea.claim_intents
            if (
                _exact_statement_text(intent.statement) in authority_statements
                or intent.claim_id in matching_claim_coordinates
            )
        ]
        if not matching_intents:
            continue
        turn_index = max(
            [transition.turn_index for transition in idea.status_history]
            + [0]
        ) + 1
        additions: List[ProofIdeaClaimResolution] = []
        for intent in matching_intents:
            current = idea.current_claim_resolution(intent.claim_id)
            if (
                current is not None
                and current.status == "invalidated"
                and current.authority == "lean"
                and current.evidence_id == evidence_id
            ):
                continue
            additions.append(
                ProofIdeaClaimResolution.create(
                    proof_idea_id=idea_id,
                    occurrence_key=f"authoritative-negation:{evidence_id}",
                    claim_id=intent.claim_id,
                    status="invalidated",
                    authority="lean",
                    reason=str(reason or "Lean certified the exact negation"),
                    evidence_id=evidence_id,
                    turn_index=turn_index,
                    node_ids=matching_node_ids,
                )
            )
        if not additions:
            continue
        updated = dossier.upsert_proof_idea(
            replace(
                idea,
                claim_resolutions=idea.claim_resolutions + tuple(additions),
            )
        )
        observation = ProofIdeaObservation.create(
            proof_idea_id=idea_id,
            occurrence_key=f"authoritative-negation:{evidence_id}",
            kind="evidence_delta",
            summary=(
                "Lean certified the exact negation of one claim formulation; "
                "retire its dependent routes and independently validate any "
                "preserved alternative formulation"
            ),
            claim_id=matching_intents[0].claim_id,
            route_id=(matching_intents[0].consumer_ids[0] if matching_intents[0].consumer_ids else ""),
            exact_lean_output=str(reason or ""),
            evidence_hash=evidence_id,
            branch_id=(
                updated.branch_provenance[0].branch_id
                if len(updated.branch_provenance) == 1
                else ""
            ),
            turn_index=turn_index,
        )
        before = len(updated.observations)
        dossier.record_proof_idea_observation(
            idea_id,
            observation,
            branch_source="authoritative_falsification",
        )
        added += len(additions) + int(
            len(dossier.proof_ideas[idea_id].observations) > before
        )
    return added


def _preserve_graph_tombstone_certificate(node: Any) -> None:
    if getattr(node, "status", "") != "proved":
        return
    node.metadata["superseded_previous_status"] = "proved"
    proof_hash = str(getattr(node, "proof_hash", "") or "").strip()
    if proof_hash:
        node.metadata.setdefault("superseded_previous_proof_hash", proof_hash)
    source_hash = str(getattr(node, "source_hash", "") or "").strip()
    if source_hash:
        node.metadata.setdefault("superseded_previous_source_hash", source_hash)


_AUTHORITATIVE_FALSIFICATION_STATE_SNAPSHOT = (
    "authoritative_falsification_previous_state"
)
_AUTHORITATIVE_FALSIFICATION_METADATA_KEYS = {
    "proposal_superseded",
    "proposal_invalidated",
    "invalidated_statement_key",
    "invalid_reason",
    "authoritative_falsification_terminal",
    "authoritative_falsification_statement_key",
    "authoritative_falsification_target_environment_hash",
    "authoritative_falsification_authority_ids",
    "superseded_previous_status",
    "superseded_previous_proof_hash",
    "superseded_previous_source_hash",
    "route_retired",
    "route_dependency_contradicted",
    "route_retirement_verdict",
    "route_retired_reason",
    "route_retired_dependency_node_id",
    "route_poisoned_descendant_suppressed",
    "route_assembly_contract_last_verdict",
    "route_assembly_invalidated_reason",
    "route_assembly_invalidated_dependency_node_id",
    "invalidated_assembled_dependency_node_ids",
    "assembled_dependency_node_ids",
    "assembled_by_action",
    "assembled_route_proof_hash",
    "assembled_dependency_signature_hash",
    "assembled_branch_frame_ids",
    "route_cases_assembly_helper_names",
}


def _snapshot_authoritative_falsification_state(node: Any) -> None:
    """Capture the state that a quarantined certificate must not destroy."""

    metadata = getattr(node, "metadata", None)
    if not isinstance(metadata, dict):
        metadata = {}
        node.metadata = metadata
    if isinstance(metadata.get(_AUTHORITATIVE_FALSIFICATION_STATE_SNAPSHOT), dict):
        return
    metadata[_AUTHORITATIVE_FALSIFICATION_STATE_SNAPSHOT] = {
        "status": str(getattr(node, "status", "") or ""),
        "proof_hash": str(getattr(node, "proof_hash", "") or ""),
        "source_hash": str(getattr(node, "source_hash", "") or ""),
        "metadata": {
            key: copy.deepcopy(metadata[key])
            for key in _AUTHORITATIVE_FALSIFICATION_METADATA_KEYS
            if key in metadata
        },
    }


def _snapshot_authoritative_route_retirement_state(
    graph: Any,
    route_id: str,
) -> None:
    """Snapshot a route and descendants before certificate-only retirement."""

    clean_route_id = str(route_id or "").strip()
    if not clean_route_id:
        return
    route_ids_for_node = getattr(graph, "_node_route_ids", None)
    for node in list(getattr(graph, "nodes", {}).values()):
        belongs = str(getattr(node, "node_id", "") or "") == clean_route_id
        if not belongs and callable(route_ids_for_node):
            try:
                belongs = clean_route_id in set(route_ids_for_node(node))
            except Exception:
                belongs = False
        if belongs:
            _snapshot_authoritative_falsification_state(node)


def _restore_authoritative_falsification_state(node: Any) -> bool:
    metadata = getattr(node, "metadata", None)
    if not isinstance(metadata, dict):
        return False
    snapshot = metadata.pop(_AUTHORITATIVE_FALSIFICATION_STATE_SNAPSHOT, None)
    if (
        isinstance(snapshot, dict)
        and str(getattr(node, "status", "") or "") == "proved"
        and (
            bool(str(getattr(node, "proof_hash", "") or "").strip())
            or bool(str(metadata.get("verified_by_helper_name") or "").strip())
            or bool(
                str(metadata.get("verified_by_helper_node_id") or "").strip()
            )
        )
    ):
        # A verified fact landed after the certificate snapshot. Restoring the
        # older open/rejected state would erase monotone mathematical progress
        # and leave contradictory `open + verified_by` metadata. Drop only the
        # quarantined certificate markers and preserve the later proof.
        for key in _AUTHORITATIVE_FALSIFICATION_METADATA_KEYS:
            metadata.pop(key, None)
        return False
    if not isinstance(snapshot, dict):
        # Legacy checkpoints lack a pre-retirement snapshot. Fail open: the
        # certificate is no longer authority in this process, so an open retry
        # is safer than a permanent false tombstone.
        node.status = "open"
        node.proof_hash = ""
        for key in _AUTHORITATIVE_FALSIFICATION_METADATA_KEYS:
            metadata.pop(key, None)
        return True
    for key in _AUTHORITATIVE_FALSIFICATION_METADATA_KEYS:
        metadata.pop(key, None)
    for key, value in dict(snapshot.get("metadata") or {}).items():
        if key in _AUTHORITATIVE_FALSIFICATION_METADATA_KEYS:
            metadata[key] = copy.deepcopy(value)
    node.status = str(snapshot.get("status") or "open")
    node.proof_hash = str(snapshot.get("proof_hash") or "")
    node.source_hash = str(snapshot.get("source_hash") or "")
    return True


def _reject_graph_native_proposals_for_statement_key(
    dossier: "ProofDossier",
    statement_key: str,
    *,
    reason: str = "",
    target_environment_hash: str = "",
) -> None:
    graph = getattr(dossier, "proof_graph", None)
    key = str(statement_key or "").strip()
    if graph is None or not key:
        return
    authority_environment_hash = str(target_environment_hash or "").strip()
    if not authority_environment_hash:
        return
    full_expr_hashes = _authoritative_invalidation_full_expr_hashes(
        dossier,
        key,
        authority_environment_hash,
    )
    authority_statements = _authoritative_invalidation_statement_texts(
        dossier, key, authority_environment_hash
    )
    swept_kinds = {
        "proposed_claim",
        "formal_variant",
        "missing_obligation",
        "helper",
    }
    route_dependency_edge_kinds = {"route_requires", "route_blocked_by", "route_replan"}
    reason_text = str(reason or "")
    for node in list(getattr(graph, "nodes", {}).values()):
        if node.kind not in swept_kinds:
            continue
        direct_match = _node_matches_authoritative_invalidation(
            node,
            statement_key=key,
            target_environment_hash=authority_environment_hash,
            full_expr_hashes=full_expr_hashes,
            authority_statements=authority_statements,
        )
        parent_reference_match = _node_references_invalidated_parent(
            node, key, authority_statements=authority_statements
        )
        if not direct_match and not parent_reference_match:
            continue
        matching_authority_ids = _authority_ids_matching_node(
            dossier, node, key, authority_environment_hash
        )
        if parent_reference_match:
            node_metadata = dict(getattr(node, "metadata", {}) or {})
            matching_authority_ids.update(
                str(authority.get("authority_id") or "").strip()
                for authority in _active_authorities_for_key(
                    dossier, key, authority_environment_hash
                )
                if any(
                    _exact_statement_text(node_metadata.get(field))
                    == _exact_statement_text(authority.get("statement"))
                    for field in _INVALIDATED_PARENT_STATEMENT_FIELDS
                )
            )
            matching_authority_ids.discard("")
        if not matching_authority_ids:
            continue
        if parent_reference_match and str(
            (getattr(node, "metadata", {}) or {}).get(
                "statement_environment_hash"
            )
            or ""
        ).strip() not in {"", authority_environment_hash}:
            continue
        if (
            node.metadata.get("proposal_invalidated") is True
            and str(node.metadata.get("invalidated_statement_key") or "") == key
            and str(node.metadata.get("invalid_reason") or "") == reason_text
            and node.status in {"failed", "rejected", "blocked"}
        ):
            continue
        _snapshot_authoritative_falsification_state(node)
        route_ids = {
            str((getattr(node, "metadata", {}) or {}).get("route_id") or "").strip()
        }
        route_ids.add(
            str(
                (getattr(node, "metadata", {}) or {}).get(
                    "formalization_rejected_bridge_route_id"
                )
                or ""
            ).strip()
        )
        for edge in list(graph.incoming(node.node_id)):
            if edge.kind not in route_dependency_edge_kinds:
                continue
            route = graph.nodes.get(edge.source)
            if route is None or getattr(route, "kind", "") != "strategy_route":
                continue
            route_ids.add(route.node_id)
        for route_id in sorted(item for item in route_ids if item):
            _snapshot_authoritative_route_retirement_state(graph, route_id)
        # An executable, differently stated bridge may be the corrected
        # formulation.  Its independent clone was preserved before this sweep;
        # retire the old parent-dependent route without falsely certifying the
        # candidate itself as false.
        terminalize_node = bool(
            direct_match
            or not graph_statement_is_executable(
                str(getattr(node, "statement", "") or "")
            )
        )
        if terminalize_node:
            node.metadata["proposal_superseded"] = True
            node.metadata["proposal_invalidated"] = True
            node.metadata["invalidated_statement_key"] = key
            node.metadata["invalid_reason"] = reason_text
            node.metadata["authoritative_falsification_terminal"] = True
            node.metadata["authoritative_falsification_statement_key"] = key
            node.metadata[
                "authoritative_falsification_target_environment_hash"
            ] = authority_environment_hash
            node.metadata["authoritative_falsification_authority_ids"] = sorted(
                matching_authority_ids
            )
            if node.status == "proved":
                _preserve_graph_tombstone_certificate(node)
                node.status = "open"
                node.proof_hash = ""
            graph.record_attempt(
                node.node_id,
                phase="proposal_invalidated",
                turn_index=0,
                proof="",
                verdict="claim_invalidated_by_child",
                error_type="proposal_invalidated",
                metadata={"invalid_reason": reason_text},
            )
            _reject_replans_sourced_from_graph_node(
                graph,
                node.node_id,
                helper_name="",
                active_statement_key=key,
            )
        retire_route = getattr(graph, "retire_strategy_route", None)
        if callable(retire_route):
            for route_id in sorted(item for item in route_ids if item):
                retired = retire_route(
                    route_id,
                    reason=str(reason or "route dependency contradicted"),
                    dependency_node_id=node.node_id,
                    verdict="route_dependency_contradicted",
                )
                route = graph.nodes.get(route_id)
                if retired and route is not None:
                    route.metadata[
                        "authoritative_falsification_statement_key"
                    ] = key
                    route.metadata[
                        "authoritative_falsification_target_environment_hash"
                    ] = authority_environment_hash
                    existing_authority_ids = set(
                        route.metadata.get(
                            "authoritative_falsification_authority_ids", []
                        )
                        or []
                    )
                    route.metadata[
                        "authoritative_falsification_authority_ids"
                    ] = sorted(existing_authority_ids | matching_authority_ids)
    graph.enforce_superseded_tombstones()


def _retire_route_contracts_for_invalidated_statement_key(
    dossier: "ProofDossier",
    statement_key: str,
    *,
    reason: str = "",
    target_environment_hash: str = "",
) -> int:
    graph = getattr(dossier, "proof_graph", None)
    key = str(statement_key or "").strip()
    authority_environment_hash = str(target_environment_hash or "").strip()
    if graph is None or not key or not authority_environment_hash:
        return 0
    authority_statements = _authoritative_invalidation_statement_texts(
        dossier, key, authority_environment_hash
    )
    full_expr_hashes = _authoritative_invalidation_full_expr_hashes(
        dossier, key, authority_environment_hash
    )
    retire_route = getattr(graph, "retire_strategy_route", None)
    if not callable(retire_route):
        return 0
    retired_count = 0
    for route in list(graph.nodes_by_kind("strategy_route")):
        metadata = route.metadata if isinstance(route.metadata, dict) else {}
        if metadata.get("route_retired") or metadata.get("route_dependency_contradicted"):
            continue
        contract_claims: List[Dict[str, Any]] = []
        raw_claims = metadata.get("accepted_claims")
        if isinstance(raw_claims, list):
            contract_claims.extend(
                dict(item) for item in raw_claims if isinstance(item, dict)
            )
        contract = metadata.get("route_assembly_contract")
        if isinstance(contract, dict):
            contract_metadata = contract.get("metadata")
            if isinstance(contract_metadata, dict):
                raw_contract_claims = contract_metadata.get("accepted_claims")
                if isinstance(raw_contract_claims, list):
                    contract_claims.extend(
                        dict(item)
                        for item in raw_contract_claims
                        if isinstance(item, dict)
                    )
        for claim in contract_claims:
            statement = str(claim.get("statement") or "").strip()
            dependency_node_id = str(claim.get("claim_node_id") or "").strip()
            dependency_node = graph.nodes.get(dependency_node_id)
            if (
                dependency_node is None
                or str(
                    (getattr(dependency_node, "metadata", {}) or {}).get(
                        "statement_environment_hash"
                    )
                    or ""
                ).strip()
                != authority_environment_hash
            ):
                # A route claim without a live, exactly stamped target is not
                # authority-compatible.  Surface syntax alone cannot retire
                # the route after an environment change.
                continue
            if not (
                statement in authority_statements
                or _node_matches_authoritative_invalidation(
                    dependency_node,
                    statement_key=key,
                    target_environment_hash=authority_environment_hash,
                    full_expr_hashes=full_expr_hashes,
                    authority_statements=authority_statements,
                )
            ):
                continue
            matching_authority_ids = _authority_ids_matching_node(
                dossier, dependency_node, key, authority_environment_hash
            )
            if not matching_authority_ids:
                continue
            _snapshot_authoritative_route_retirement_state(graph, route.node_id)
            if retire_route(
                route.node_id,
                reason=str(reason or "route dependency contradicted"),
                dependency_node_id=dependency_node_id,
                verdict="route_dependency_contradicted",
            ):
                route.metadata[
                    "authoritative_falsification_statement_key"
                ] = key
                route.metadata[
                    "authoritative_falsification_target_environment_hash"
                ] = authority_environment_hash
                route.metadata[
                    "authoritative_falsification_authority_ids"
                ] = sorted(matching_authority_ids)
                retired_count += 1
            break
    if retired_count:
        dossier.increment_tool_metric(
            "mini_recursive_false_parent_routes_poisoned",
            retired_count,
        )
    return retired_count


def _release_unverified_falsification_tombstones(
    dossier: "ProofDossier",
) -> Dict[str, List[str]]:
    """Reopen graph work whose serialized certificate awaits fresh replay.

    The report ledger is durable evidence history, not process-local Lean
    authority. ``from_record`` deliberately drops fresh-certificate
    invalidation provenance and queues certificates for replay; graph
    tombstones created by that authority must be dropped at the same boundary.
    Verified-negative-helper invalidations remain active and are not touched.
    """

    graph = getattr(dossier, "proof_graph", None)
    if graph is None:
        return {"reopened_node_ids": [], "reopened_route_ids": []}
    active_authorities = {
        (
            canonical_dossier_statement_key(authority.get("statement") or ""),
            str(authority.get("target_environment_hash") or "").strip(),
        )
        for authority in dict(
            getattr(dossier, "mini_authoritative_negations", {}) or {}
        ).values()
        if isinstance(authority, Mapping)
        and canonical_dossier_statement_key(authority.get("statement") or "")
        and str(authority.get("target_environment_hash") or "").strip()
    }
    released_target_ids: set[str] = set()
    # Keep route-only closures recoverable even if a stale checkpoint omitted
    # the exact target node but retained its route contract and pending
    # certificate.
    pending_authorities: set[tuple[str, str]] = {
        (
            canonical_dossier_statement_key(
                str(certificate.get("statement") or "")
            ),
            str(pending.get("target_environment_hash") or "").strip(),
        )
        for pending in list(
            getattr(dossier, "mini_falsification_pending_certificates", []) or []
        )
        if isinstance(pending, dict)
        for certificate in [pending.get("certificate")]
        if isinstance(certificate, dict)
    }
    pending_authorities = {
        item for item in pending_authorities if item[0]
    }
    # A quarantined certificate is not authority after restore.  Release its
    # route whenever the exact (statement, target-environment) pair is absent;
    # same-surface authority from another environment cannot keep it closed.
    released_keys: set[str] = {
        key
        for key, environment_hash in pending_authorities
        if not environment_hash
        or (key, environment_hash) not in active_authorities
    }
    for node in list(getattr(graph, "nodes", {}).values()):
        metadata = dict(getattr(node, "metadata", {}) or {})
        key = str(metadata.get("invalidated_statement_key") or "").strip()
        node_environment_hash = str(
            metadata.get("statement_environment_hash") or ""
        ).strip()
        if (
            metadata.get("authoritative_falsification_terminal") is not True
            or not key
            or (key, node_environment_hash) in active_authorities
        ):
            continue
        released_target_ids.add(str(getattr(node, "node_id", "") or ""))
        released_keys.add(key)

    released_route_ids: set[str] = set()
    route_dependency_edge_kinds = {"route_requires", "route_blocked_by", "route_replan"}
    for route in list(graph.nodes_by_kind("strategy_route")):
        metadata = dict(getattr(route, "metadata", {}) or {})
        if not (
            metadata.get("route_retired")
            or metadata.get("route_dependency_contradicted")
        ):
            continue
        route_authority_key = str(
            metadata.get("authoritative_falsification_statement_key") or ""
        ).strip()
        route_authority_environment_hash = str(
            metadata.get(
                "authoritative_falsification_target_environment_hash"
            )
            or ""
        ).strip()
        linked_to_released_target = bool(
            route_authority_key
            and route_authority_environment_hash
            and (
                route_authority_key,
                route_authority_environment_hash,
            )
            not in active_authorities
        )
        dependency_id = str(
            metadata.get("route_retired_dependency_node_id") or ""
        ).strip()
        linked_to_released_target = bool(
            linked_to_released_target
            or dependency_id in released_target_ids
        )
        if not linked_to_released_target:
            linked_to_released_target = any(
                str(edge.target or "") in released_target_ids
                and str(edge.kind or "") in route_dependency_edge_kinds
                for edge in list(graph.outgoing(route.node_id))
            )
        if not linked_to_released_target and released_keys:
            contract_claims: List[Dict[str, Any]] = []
            contract_claims.extend(
                dict(item)
                for item in list(metadata.get("accepted_claims") or [])
                if isinstance(item, dict)
            )
            contract = metadata.get("route_assembly_contract")
            contract_metadata = (
                dict(contract.get("metadata") or {})
                if isinstance(contract, dict)
                else {}
            )
            contract_claims.extend(
                dict(item)
                for item in list(contract_metadata.get("accepted_claims") or [])
                if isinstance(item, dict)
            )
            linked_to_released_target = any(
                canonical_dossier_statement_key(
                    str(claim.get("statement") or "")
                )
                in released_keys
                for claim in contract_claims
            )
        if linked_to_released_target:
            released_route_ids.add(route.node_id)

    reopened_nodes: List[str] = []
    # Restore target nodes first. A route snapshot taken after target mutation
    # is never allowed to overwrite their original pre-certificate state.
    for node_id in sorted(released_target_ids):
        node = graph.nodes.get(node_id)
        if node is not None and _restore_authoritative_falsification_state(node):
            reopened_nodes.append(node_id)
    for route_id in sorted(released_route_ids):
        route = graph.nodes.get(route_id)
        if route is not None and _restore_authoritative_falsification_state(route):
            reopened_nodes.append(route_id)
        route_ids_for_node = getattr(graph, "_node_route_ids", None)
        for node in list(getattr(graph, "nodes", {}).values()):
            if node.node_id in released_target_ids or node.node_id == route_id:
                continue
            metadata = dict(getattr(node, "metadata", {}) or {})
            belongs_to_released_route = False
            if callable(route_ids_for_node):
                try:
                    belongs_to_released_route = route_id in set(
                        route_ids_for_node(node)
                    )
                except Exception:
                    belongs_to_released_route = False
            if not belongs_to_released_route:
                belongs_to_released_route = (
                    str(metadata.get("route_id") or "").strip() == route_id
                )
            if not (
                belongs_to_released_route
                and isinstance(
                    metadata.get(_AUTHORITATIVE_FALSIFICATION_STATE_SNAPSHOT),
                    dict,
                )
            ):
                continue
            if _restore_authoritative_falsification_state(node):
                reopened_nodes.append(node.node_id)
    repair = getattr(graph, "_repair_indexes", None)
    if callable(repair):
        repair()
    return {
        "reopened_node_ids": list(dict.fromkeys(reopened_nodes)),
        "reopened_route_ids": sorted(released_route_ids),
    }


def _supersede_stale_graph_native_proposals_for_helper_name(
    dossier: "ProofDossier",
    helper_name: str,
    *,
    active_statement_key: str,
    superseded_statement_keys: Iterable[str] = (),
    superseding_node_id: str = "",
    phase: str = "proposal_superseded_by_rebank",
) -> None:
    """Retire known prior statements from one proposed-helper registry entry.

    An LLM-chosen helper name is not lineage authority.  Callers must provide
    the statement keys held by the concrete ``ProposedHelper`` entry they are
    replacing; same-name graph work outside that registry entry survives.
    """

    graph = getattr(dossier, "proof_graph", None)
    name = str(helper_name or "").strip()
    key = str(active_statement_key or "").strip()
    stale_keys = {
        str(statement_key or "").strip()
        for statement_key in superseded_statement_keys
        if str(statement_key or "").strip()
    }
    stale_keys.discard(key)
    if graph is None or not name or not key or not stale_keys:
        return
    for node in list(getattr(graph, "nodes", {}).values()):
        if node.kind not in {"proposed_claim", "formal_variant"}:
            continue
        metadata = node.metadata
        if str(metadata.get("proposed_helper_name") or "").strip() != name:
            continue
        if graph.is_superseded_tombstone(node):
            continue
        node_statement_key = canonical_dossier_statement_key(node.statement)
        if node_statement_key == key or node_statement_key not in stale_keys:
            continue
        if graph._proved_node_has_durable_certificate(node):
            metadata["proved_proposal_preserved_from_name_reuse"] = key
            continue
        if superseding_node_id:
            graph.add_edge(node.node_id, superseding_node_id, "proposal_superseded_by")
        metadata["proposal_superseded"] = True
        metadata["superseded_active_statement_key"] = key
        graph.record_attempt(
            node.node_id,
            phase=phase,
            turn_index=0,
            proof="",
            verdict="proof_policy_rejected",
            error_type="proposal_superseded",
            metadata={
                "helper_name": name,
                "active_statement_key": key,
            },
        )
        _reject_replans_sourced_from_graph_node(
            graph,
            node.node_id,
            superseding_node_id=superseding_node_id,
            helper_name=name,
            active_statement_key=key,
        )
    graph.enforce_superseded_tombstones()


def _supersede_graph_native_proposals_for_helper_name(
    dossier: "ProofDossier",
    helper_name: str,
    *,
    verified_statement_key: str,
    superseded_statement_keys: Iterable[str] = (),
    verified_node_id: str = "",
) -> None:
    _supersede_stale_graph_native_proposals_for_helper_name(
        dossier,
        helper_name,
        active_statement_key=verified_statement_key,
        superseded_statement_keys=superseded_statement_keys,
        superseding_node_id=verified_node_id,
        phase="proposal_superseded_by_verified_helper",
    )


def _reject_replans_sourced_from_graph_node(
    graph: ProofGraph,
    node_id: str,
    *,
    superseding_node_id: str = "",
    helper_name: str = "",
    active_statement_key: str = "",
) -> None:
    source_id = str(node_id or "").strip()
    if not source_id:
        return
    obligation_ids = {
        edge.target for edge in graph.outgoing(source_id, kind="failure_requires")
    }
    replan_ids = {
        edge.target for edge in graph.outgoing(source_id, kind="needs_replan")
    }
    route_ids = {
        edge.source
        for edge in graph.incoming(source_id)
        if edge.kind in {"route_requires", "route_blocked_by"}
    }
    for route_id in route_ids:
        obligation_ids.update(
            edge.target for edge in graph.outgoing(route_id, kind="route_blocked_by")
        )
        replan_ids.update(
            edge.target for edge in graph.outgoing(route_id, kind="route_replan")
        )
    for obligation in graph.nodes_by_kind("missing_obligation"):
        metadata = dict(getattr(obligation, "metadata", {}) or {})
        source = str(metadata.get("source_node_id") or "").strip()
        route = str(metadata.get("route_id") or "").strip()
        if source == source_id or source in route_ids or route in route_ids:
            obligation_ids.add(obligation.node_id)
    for obligation_id in obligation_ids:
        obligation = graph.nodes.get(obligation_id)
        if obligation is None or obligation.kind != "missing_obligation":
            continue
        if superseding_node_id:
            graph.add_edge(
                obligation.node_id, superseding_node_id, "proposal_superseded_by"
            )
        obligation.metadata["proposal_superseded"] = True
        obligation.metadata["superseded_source_node_id"] = source_id
        if obligation.status == "proved":
            _preserve_graph_tombstone_certificate(obligation)
            obligation.status = "open"
            obligation.proof_hash = ""
        graph.record_attempt(
            obligation.node_id,
            phase="obligation_superseded_by_proposal_rebank",
            turn_index=0,
            proof="",
            verdict="proof_policy_rejected",
            error_type="proposal_superseded",
            metadata={
                "source_node_id": source_id,
                "helper_name": str(helper_name or ""),
                "active_statement_key": str(active_statement_key or ""),
            },
        )
        replan_ids.update(
            edge.target
            for edge in graph.outgoing(
                obligation.node_id,
                kind="obligation_replan",
            )
        )
    for replan in graph.nodes_by_kind("replan_queue_item"):
        metadata = dict(getattr(replan, "metadata", {}) or {})
        source = str(metadata.get("source_node_id") or "").strip()
        route = str(metadata.get("route_id") or "").strip()
        obligation = str(metadata.get("obligation_id") or "").strip()
        if (
            source == source_id
            or source in route_ids
            or route in route_ids
            or obligation in obligation_ids
        ):
            replan_ids.add(replan.node_id)
    for replan_id in replan_ids:
        replan = graph.nodes.get(replan_id)
        if replan is None or replan.kind != "replan_queue_item":
            continue
        if superseding_node_id:
            graph.add_edge(replan.node_id, superseding_node_id, "proposal_superseded_by")
        replan.metadata["proposal_superseded"] = True
        replan.metadata["superseded_source_node_id"] = source_id
        if replan.status == "proved":
            _preserve_graph_tombstone_certificate(replan)
            replan.status = "open"
            replan.proof_hash = ""
        graph.record_attempt(
            replan.node_id,
            phase="replan_superseded_by_proposal_rebank",
            turn_index=0,
            proof="",
            verdict="proof_policy_rejected",
            error_type="proposal_superseded",
            metadata={
                "source_node_id": source_id,
                "helper_name": str(helper_name or ""),
                "active_statement_key": str(active_statement_key or ""),
            },
        )


def _supersede_unmatched_child_variants_for_active_claim(
    graph: ProofGraph,
    *,
    claim_node_id: str,
    active_statement_key: str,
    helper_name: str,
    superseding_node_id: str = "",
    phase: str = "variant_superseded_by_active_claim",
) -> None:
    claim_id = str(claim_node_id or "").strip()
    key = str(active_statement_key or "").strip()
    if not claim_id or not key:
        return
    claim = graph.nodes.get(claim_id)
    if claim is None or canonical_dossier_statement_key(claim.statement) != key:
        return
    graph._supersede_unmatched_child_variants_for_claim(
        claim_node_id=claim_id,
        active_statement=claim.statement,
        helper_node_id=str(superseding_node_id or "").strip(),
        helper_name=str(helper_name or "").strip(),
    )


def _resolve_graph_native_obligations_for_statement_key(
    dossier: "ProofDossier",
    *,
    statement_key: str,
    verified_helper_name: str,
    verified_node_id: str,
    source_hash: str,
    proof_hash: str,
    support_names: Iterable[str],
    resolved_obligation_node_ids: Optional[List[str]] = None,
) -> int:
    graph = getattr(dossier, "proof_graph", None)
    key = str(statement_key or "").strip()
    if graph is None or not key:
        return 0
    resolved = 0
    helper_node = graph.nodes.get(str(verified_node_id or "").strip())
    helper_render_policy = str(
        (getattr(helper_node, "metadata", {}) or {}).get(
            "verified_helper_render_policy"
        )
        or ""
    ).strip()
    count_exact_negative_metric = helper_render_policy == "advisory_negative_evidence"
    support_list = [
        str(name or "").strip() for name in support_names if str(name or "").strip()
    ]
    current_helper_node_id = str(verified_node_id or "").strip()
    for obligation in graph.nodes_by_kind("missing_obligation"):
        if canonical_dossier_statement_key(obligation.statement) != key:
            continue
        prior_status = str(getattr(obligation, "status", "") or "")
        prior_helper_node_id = str(
            (obligation.metadata or {}).get("verified_by_helper_node_id") or ""
        ).strip()
        if (
            prior_status == "proved"
            and prior_helper_node_id
            and prior_helper_node_id != current_helper_node_id
        ):
            continue
        graph.mark_obligation_proved_by_helper(
            obligation.node_id,
            verified_node_id,
            source_hash=source_hash,
            proof_hash=proof_hash,
            support_names=support_list,
        )
        if (
            obligation.status == "proved"
            and str((obligation.metadata or {}).get("verified_by_helper_node_id") or "")
            == current_helper_node_id
        ):
            obligation.metadata["verified_statement_key"] = key
            newly_resolved = prior_status != "proved"
            already_proved_by_current_helper = bool(
                prior_status == "proved" and prior_helper_node_id == current_helper_node_id
            )
            if (
                (newly_resolved or already_proved_by_current_helper)
                and resolved_obligation_node_ids is not None
                and obligation.node_id not in resolved_obligation_node_ids
            ):
                resolved_obligation_node_ids.append(obligation.node_id)
            if count_exact_negative_metric:
                if not bool(
                    obligation.metadata.get(
                        "negative_evidence_exact_certificate_metric_recorded"
                    )
                ):
                    obligation.metadata[
                        "negative_evidence_exact_certificate_metric_recorded"
                    ] = True
                    resolved += 1
            else:
                resolved += 1
        elif obligation.status != "proved":
            obligation.metadata.pop("verified_by_helper_name", None)
            obligation.metadata.pop("verified_by_helper_node_id", None)
            obligation.metadata.pop("verified_statement_key", None)
    return resolved


def _resolve_graph_native_claims_for_statement_key(
    dossier: "ProofDossier",
    *,
    statement_key: str,
    verified_helper_name: str,
    verified_node_id: str,
    source_hash: str,
    proof_hash: str,
    support_names: Iterable[str],
    resolved_claim_node_ids: Optional[List[str]] = None,
    resolved_variant_node_ids: Optional[List[str]] = None,
) -> int:
    graph = getattr(dossier, "proof_graph", None)
    key = str(statement_key or "").strip()
    if graph is None or not key:
        return 0
    resolved = 0
    helper_node = graph.nodes.get(str(verified_node_id or "").strip())
    helper_render_policy = str(
        (getattr(helper_node, "metadata", {}) or {}).get(
            "verified_helper_render_policy"
        )
        or ""
    ).strip()
    count_exact_negative_metric = helper_render_policy == "advisory_negative_evidence"
    support_list = [
        str(name or "").strip() for name in support_names if str(name or "").strip()
    ]
    current_helper_node_id = str(verified_node_id or "").strip()
    for claim_node in graph.nodes_by_kind("proposed_claim"):
        if bool((claim_node.metadata or {}).get("proposal_superseded")):
            continue
        if canonical_dossier_statement_key(claim_node.statement) != key:
            continue
        prior_status = str(getattr(claim_node, "status", "") or "")
        prior_helper_node_id = str(
            (claim_node.metadata or {}).get("verified_by_helper_node_id") or ""
        ).strip()
        if (
            prior_status == "proved"
            and prior_helper_node_id
            and prior_helper_node_id != current_helper_node_id
        ):
            continue
        graph.mark_claim_proved_by_helper(
            claim_node.node_id,
            verified_node_id,
            source_hash=source_hash,
            proof_hash=proof_hash,
            support_names=support_list,
        )
        certified_by_current_helper = bool(
            claim_node.status == "proved"
            and str((claim_node.metadata or {}).get("verified_by_helper_node_id") or "")
            == current_helper_node_id
        )
        if certified_by_current_helper:
            claim_node.metadata["verified_by_helper_name"] = str(
                verified_helper_name or ""
            ).strip()
            newly_resolved = prior_status != "proved"
            already_proved_by_current_helper = bool(
                prior_status == "proved" and prior_helper_node_id == current_helper_node_id
            )
            if (
                (newly_resolved or already_proved_by_current_helper)
                and resolved_claim_node_ids is not None
                and claim_node.node_id not in resolved_claim_node_ids
            ):
                resolved_claim_node_ids.append(claim_node.node_id)
            if count_exact_negative_metric:
                if not bool(
                    claim_node.metadata.get(
                        "negative_evidence_exact_certificate_metric_recorded"
                    )
                ):
                    claim_node.metadata[
                        "negative_evidence_exact_certificate_metric_recorded"
                    ] = True
                    resolved += 1
            else:
                resolved += 1
            _supersede_unmatched_child_variants_for_active_claim(
                graph,
                claim_node_id=claim_node.node_id,
                active_statement_key=key,
                helper_name=verified_helper_name,
                superseding_node_id=verified_node_id,
                phase="variant_superseded_by_verified_claim",
            )
        elif claim_node.status != "proved":
            claim_node.metadata.pop("verified_by_helper_name", None)
            claim_node.metadata.pop("verified_by_helper_node_id", None)
    for variant_node in graph.nodes_by_kind("formal_variant"):
        if bool((variant_node.metadata or {}).get("proposal_superseded")):
            continue
        if canonical_dossier_statement_key(variant_node.statement) != key:
            continue
        prior_status = str(getattr(variant_node, "status", "") or "")
        prior_helper_node_id = str(
            (variant_node.metadata or {}).get("verified_by_helper_node_id") or ""
        ).strip()
        if (
            prior_status == "proved"
            and prior_helper_node_id
            and prior_helper_node_id != current_helper_node_id
        ):
            continue
        graph.mark_variant_proved_by_helper(
            variant_node.node_id,
            verified_node_id,
            source_hash=source_hash,
            proof_hash=proof_hash,
            support_names=support_list,
        )
        certified_by_current_helper = bool(
            variant_node.status == "proved"
            and str((variant_node.metadata or {}).get("verified_by_helper_node_id") or "")
            == current_helper_node_id
        )
        if certified_by_current_helper:
            variant_node.metadata["verified_by_helper_name"] = str(
                verified_helper_name or ""
            ).strip()
            newly_resolved = prior_status != "proved"
            already_proved_by_current_helper = bool(
                prior_status == "proved" and prior_helper_node_id == current_helper_node_id
            )
            if (
                (newly_resolved or already_proved_by_current_helper)
                and resolved_variant_node_ids is not None
                and variant_node.node_id not in resolved_variant_node_ids
            ):
                resolved_variant_node_ids.append(variant_node.node_id)
            if count_exact_negative_metric:
                if not bool(
                    variant_node.metadata.get(
                        "negative_evidence_exact_certificate_metric_recorded"
                    )
                ):
                    variant_node.metadata[
                        "negative_evidence_exact_certificate_metric_recorded"
                    ] = True
                    resolved += 1
            else:
                resolved += 1
        elif variant_node.status != "proved":
            variant_node.metadata.pop("verified_by_helper_name", None)
            variant_node.metadata.pop("verified_by_helper_node_id", None)
    return resolved


def _retire_graph_native_positive_targets_for_negative_evidence(
    dossier: "ProofDossier",
    *,
    negated_statement_key: str,
    verified_helper_name: str,
    verified_node_id: str,
    statement: str,
    source_hash: str,
    evidence_environment_hash: str,
) -> Tuple[int, int]:
    """Record advisory negative evidence without granting disproof authority.

    A verified helper proves its own declaration, but this path does not carry
    the complete axiom-audited falsification report required by the central
    authority admission boundary. In particular, parsing ``¬ P`` back into
    ``P`` and canonicalizing it is not an identity proof. The falsification
    action may independently certify and promote the exact positive target.
    """

    graph = getattr(dossier, "proof_graph", None)
    key = str(negated_statement_key or "").strip()
    authority_environment_hash = str(evidence_environment_hash or "").strip()
    if graph is None or not key or not authority_environment_hash:
        return 0, 0
    for node in list(getattr(graph, "nodes", {}).values()):
        if node.kind not in {"proposed_claim", "formal_variant", "missing_obligation"}:
            continue
        if bool((getattr(node, "metadata", {}) or {}).get("proposal_superseded")):
            continue
        if canonical_dossier_statement_key(getattr(node, "statement", "") or "") != key:
            continue
        if str(
            (getattr(node, "metadata", {}) or {}).get(
                "statement_environment_hash"
            )
            or ""
        ).strip() != authority_environment_hash:
            continue
        node.metadata["negative_evidence_advisory_only"] = True
        node.metadata["negative_evidence_helper_name"] = str(
            verified_helper_name or ""
        ).strip()
        node.metadata["negative_evidence_helper_node_id"] = str(
            verified_node_id or ""
        ).strip()
        node.metadata["negative_evidence_statement"] = str(statement or "").strip()
        node.metadata["negative_evidence_statement_key"] = key
        node.metadata["negative_evidence_source_hash"] = str(source_hash or "").strip()
    return 0, 0


def _resolve_graph_native_obligations_against_verified_helpers(
    dossier: "ProofDossier",
    *,
    statement_key: str = "",
) -> None:
    graph = getattr(dossier, "proof_graph", None)
    if graph is None:
        return
    target_key = str(statement_key or "").strip()
    for helper in list(getattr(dossier, "verified_helpers", {}).values()):
        helper_exact_negative = (
            str(getattr(helper, "render_policy", "") or "").strip()
            == "advisory_negative_evidence"
        )
        helper_statement_key = canonical_dossier_statement_key(
            helper_decl_statement(helper.source)
        )
        if not helper_statement_key:
            continue
        if target_key and helper_statement_key != target_key:
            continue
        resolved_claim_node_ids: List[str] = []
        resolved_variant_node_ids: List[str] = []
        resolved_obligation_node_ids: List[str] = []
        exact_negative_certificates = 0
        if dossier._verified_helper_context_visible(helper) or helper_exact_negative:
            exact_negative_certificates += _resolve_graph_native_claims_for_statement_key(
                dossier,
                statement_key=helper_statement_key,
                verified_helper_name=helper.name,
                verified_node_id=graph.helper_name_to_node_id.get(helper.name, ""),
                source_hash=helper.source_hash,
                proof_hash=helper.source_hash,
                support_names=list(helper.support_names),
                resolved_claim_node_ids=resolved_claim_node_ids,
                resolved_variant_node_ids=resolved_variant_node_ids,
            )
        exact_negative_certificates += _resolve_graph_native_obligations_for_statement_key(
            dossier,
            statement_key=helper_statement_key,
            verified_helper_name=helper.name,
            verified_node_id=graph.helper_name_to_node_id.get(helper.name, ""),
            source_hash=helper.source_hash,
            proof_hash=helper.source_hash,
            support_names=list(helper.support_names),
            resolved_obligation_node_ids=resolved_obligation_node_ids,
        )
        if (
            resolved_claim_node_ids
            or resolved_variant_node_ids
            or resolved_obligation_node_ids
        ):
            _merge_verified_helper_progress_delta(
                dossier,
                helper,
                statement_key=helper_statement_key,
                resolved_claim_node_ids=resolved_claim_node_ids,
                resolved_variant_node_ids=resolved_variant_node_ids,
                resolved_obligation_node_ids=resolved_obligation_node_ids,
            )
        if helper_exact_negative and exact_negative_certificates:
            dossier.increment_tool_metric(
                "mini_graph_negative_evidence_exact_certificates_accepted",
                exact_negative_certificates,
            )


def strong_progress_for_accepted_helpers(
    dossier: Any,
    accepted_helper_names: Iterable[str],
) -> bool:
    """Return whether accepted helpers created verified parent/root impact."""

    return bool(
        helper_progress_metadata_for_accepted_helpers(
            dossier, accepted_helper_names
        ).get("parent_progress")
    )


def theory_progress_for_accepted_helpers(
    dossier: Any,
    accepted_helper_names: Iterable[str],
) -> bool:
    """Return whether accepted helpers added novel reusable local theory."""

    return bool(
        helper_progress_metadata_for_accepted_helpers(
            dossier, accepted_helper_names
        ).get("theory_progress")
    )


def _coerce_verified_helper_progress_delta(
    raw: Any,
) -> Optional[VerifiedHelperProgressDelta]:
    if isinstance(raw, VerifiedHelperProgressDelta):
        return raw
    if not isinstance(raw, dict):
        return None
    helper_name = str(raw.get("helper_name") or "").strip()
    if not helper_name:
        return None
    return VerifiedHelperProgressDelta(
        helper_name=helper_name,
        statement_key=str(raw.get("statement_key") or "").strip(),
        canonical_helper_name=str(raw.get("canonical_helper_name") or "").strip(),
        theory_progress=bool(raw.get("theory_progress")),
        resolved_claim_node_ids=[
            str(item or "").strip()
            for item in list(raw.get("resolved_claim_node_ids") or [])
            if str(item or "").strip()
        ],
        resolved_variant_node_ids=[
            str(item or "").strip()
            for item in list(raw.get("resolved_variant_node_ids") or [])
            if str(item or "").strip()
        ],
        resolved_obligation_node_ids=[
            str(item or "").strip()
            for item in list(raw.get("resolved_obligation_node_ids") or [])
            if str(item or "").strip()
        ],
    )


def _accepted_helper_delta_names(
    dossier: Any,
    accepted_helper_names: Iterable[str],
) -> List[str]:
    names = [str(name or "").strip() for name in (accepted_helper_names or ())]
    return [name for name in names if name]


def _verified_helper_counts_for_theory_progress(
    dossier: Any,
    helper: Any,
) -> bool:
    if verified_helper_is_premise_projection(helper):
        return False
    if not verified_helper_admission_quality(helper).generic_novelty:
        return False
    visible_fn = getattr(dossier, "_verified_helper_context_visible", None)
    visible = bool(visible_fn(helper)) if callable(visible_fn) else True
    render_policy = str(getattr(helper, "render_policy", "") or "").strip()
    return bool(visible or render_policy == "advisory_root_equivalent")


def verified_helper_is_premise_projection(helper: Any) -> bool:
    """Return whether a helper merely projects one of its own assumptions.

    A theorem such as ``(h : P) -> P`` is valid and can remain useful as a
    local declaration, but it establishes no new proposition relative to the
    context required to apply it.  Keep that distinction independent of the
    helper's visibility policy: visibility controls Lean reuse, while this
    predicate controls substantive progress and durable cache seeding.

    Recompute from the statement as a fail-safe for old checkpoints and
    duck-typed cache callers whose quality tags predate this classification.
    """

    quality_tags = (
        helper.get("quality_tags", ())
        if isinstance(helper, Mapping)
        else getattr(helper, "quality_tags", ())
    )
    if "premise_projection_helper" in {
        str(tag or "").strip() for tag in list(quality_tags or ())
    }:
        return True
    source = (
        str(
            helper.get("source")
            or helper.get("declaration")
            or helper.get("code")
            or ""
        ).strip()
        if isinstance(helper, Mapping)
        else (
            str(helper or "").strip()
            if isinstance(helper, str)
            else str(getattr(helper, "source", "") or "").strip()
        )
    )
    statement = helper_decl_statement(source) if source else ""
    if not statement:
        statement = str(
            (
                helper.get("statement", "")
                if isinstance(helper, Mapping)
                else getattr(helper, "statement", "")
            )
            or ""
        ).strip()
    return bool(statement and graph_statement_has_circular_premise(statement))


def _helper_progress_parent_node_ids(
    dossier: Any,
    *,
    helper_name: str,
    delta: Optional[VerifiedHelperProgressDelta],
) -> Tuple[List[str], List[str], List[str]]:
    graph = getattr(dossier, "proof_graph", None)
    helpers = getattr(dossier, "verified_helpers", {}) or {}
    helper = helpers.get(helper_name) if isinstance(helpers, dict) else None
    if graph is None or helper is None:
        return [], [], []
    if verified_helper_is_premise_projection(helper):
        return [], [], []
    # Exact-scope graph authorization is allowed to close the exact target,
    # but it is not reusable mathematical progress.  Recompute here so stale
    # or externally-produced progress deltas cannot convert that local closure
    # into parent/strong credit after restore.
    if not verified_helper_admission_quality(helper).generic_novelty:
        return [], [], []

    render_policy = str(getattr(helper, "render_policy", "") or "").strip()
    visible_fn = getattr(dossier, "_verified_helper_context_visible", None)
    visible = bool(visible_fn(helper)) if callable(visible_fn) else True
    if not visible and render_policy not in {
        "advisory_negative_evidence",
        "advisory_root_equivalent",
    }:
        return [], [], []

    helper_node_id = str(
        (getattr(graph, "helper_name_to_node_id", {}) or {}).get(helper_name) or ""
    ).strip()
    if not helper_node_id:
        return [], [], []

    statement_key = (
        str(getattr(delta, "statement_key", "") or "").strip()
        if delta is not None
        else ""
    )
    if not statement_key:
        statement_key = canonical_dossier_statement_key(
            helper_decl_statement(getattr(helper, "source", "") or "")
        )

    def valid_node(raw_node_id: str, kind: str) -> Optional[str]:
        node_id = str(raw_node_id or "").strip()
        node = graph.nodes.get(node_id) if node_id else None
        if node is None or getattr(node, "kind", "") != kind:
            return None
        metadata = getattr(node, "metadata", {}) or {}
        if str(getattr(node, "status", "") or "") != "proved":
            return None
        is_superseded = getattr(graph, "is_superseded_tombstone", None)
        if callable(is_superseded) and bool(is_superseded(node)):
            return None
        if bool(
            metadata.get("proposal_superseded")
            or metadata.get("route_retired")
            or metadata.get("route_dependency_contradicted")
        ):
            return None
        if str(metadata.get("verified_by_helper_node_id") or "").strip() != helper_node_id:
            return None
        if statement_key and canonical_dossier_statement_key(node.statement) != statement_key:
            return None
        return node_id

    def append_valid(target: List[str], raw_node_id: str, kind: str) -> None:
        node_id = valid_node(raw_node_id, kind)
        if node_id and node_id not in target:
            target.append(node_id)

    claim_ids: List[str] = []
    variant_ids: List[str] = []
    obligation_ids: List[str] = []
    if delta is not None:
        for node_id in delta.resolved_claim_node_ids:
            append_valid(claim_ids, node_id, "proposed_claim")
        for node_id in delta.resolved_variant_node_ids:
            append_valid(variant_ids, node_id, "formal_variant")
        for node_id in delta.resolved_obligation_node_ids:
            append_valid(obligation_ids, node_id, "missing_obligation")

    for node in list(getattr(graph, "nodes", {}).values()):
        kind = str(getattr(node, "kind", "") or "")
        if kind == "proposed_claim":
            append_valid(claim_ids, node.node_id, "proposed_claim")
        elif kind == "formal_variant":
            append_valid(variant_ids, node.node_id, "formal_variant")
        elif kind == "missing_obligation":
            append_valid(obligation_ids, node.node_id, "missing_obligation")
    return claim_ids, variant_ids, obligation_ids


def helper_progress_metadata_for_accepted_helpers(
    dossier: Any,
    accepted_helper_names: Iterable[str],
) -> Dict[str, Any]:
    """Aggregate durable theory/parent progress for accepted helpers.

    ``theory_progress`` means the helper adds a novel visible local theorem.
    ``parent_progress`` means the helper produced graph-certified impact
    against a proposed claim, formal variant, or missing obligation. Only the
    latter is allowed to drive ``strong_progress`` under strict session
    accounting.
    """

    names = _accepted_helper_delta_names(dossier, accepted_helper_names)
    deltas_raw = getattr(dossier, "verified_helper_progress_deltas", None)
    if not isinstance(deltas_raw, dict):
        deltas_raw = {}
    if not names:
        return {
            "theory_progress": False,
            "parent_progress": False,
            "strong_progress": False,
            "strong_progress_reason": "none",
            "theory_progress_helper_names": [],
            "parent_progress_helper_names": [],
            "parent_progress_resolved_claim_node_ids": [],
            "parent_progress_resolved_variant_node_ids": [],
            "parent_progress_resolved_obligation_node_ids": [],
            "parent_progress_edge_count": 0,
        }

    theory_names: List[str] = []
    parent_names: List[str] = []
    claim_ids: List[str] = []
    variant_ids: List[str] = []
    obligation_ids: List[str] = []
    for name in names:
        delta = _coerce_verified_helper_progress_delta(deltas_raw.get(name))
        helpers = getattr(dossier, "verified_helpers", {}) or {}
        helper = helpers.get(name) if isinstance(helpers, dict) else None
        helper_is_generic = bool(
            helper is not None
            and verified_helper_admission_quality(helper).generic_novelty
        )
        if (
            delta is not None
            and delta.theory_progress
            and helper_is_generic
            and name not in theory_names
        ):
            theory_names.append(name)
        helper_claim_ids, helper_variant_ids, helper_obligation_ids = (
            _helper_progress_parent_node_ids(
                dossier,
                helper_name=name,
                delta=delta,
            )
        )
        if helper_claim_ids or helper_variant_ids or helper_obligation_ids:
            parent_names.append(name)
            for target, source in (
                (claim_ids, helper_claim_ids),
                (variant_ids, helper_variant_ids),
                (obligation_ids, helper_obligation_ids),
            ):
                for node_id in source:
                    if node_id not in target:
                        target.append(node_id)
    parent_progress = bool(parent_names)
    theory_progress = bool(theory_names)
    reason = (
        "parent_progress"
        if parent_progress
        else "theory_progress_only"
        if theory_progress
        else "none"
    )
    return {
        "theory_progress": theory_progress,
        "parent_progress": parent_progress,
        "strong_progress": parent_progress,
        "strong_progress_reason": reason,
        "theory_progress_helper_names": theory_names,
        "parent_progress_helper_names": parent_names,
        "parent_progress_resolved_claim_node_ids": claim_ids,
        "parent_progress_resolved_variant_node_ids": variant_ids,
        "parent_progress_resolved_obligation_node_ids": obligation_ids,
        "parent_progress_edge_count": len(claim_ids) + len(variant_ids) + len(obligation_ids),
    }


def _verified_helper_for_statement_key(
    dossier: "ProofDossier",
    statement_key: str,
    *,
    verification_environment_hash: Optional[str] = None,
) -> Optional["VerifiedHelper"]:
    key = str(statement_key or "").strip()
    if not key:
        return None
    expected_environment_hash = (
        str(verification_environment_hash or "").strip()
        if verification_environment_hash is not None
        else None
    )
    for helper in list(getattr(dossier, "verified_helpers", {}).values()):
        if not dossier._verified_helper_context_visible(helper):
            continue
        if (
            expected_environment_hash is not None
            and str(helper.verification_environment_hash or "").strip()
            != expected_environment_hash
        ):
            continue
        helper_key = canonical_dossier_statement_key(helper_decl_statement(helper.source))
        if helper_key and helper_key == key:
            return helper
    return None


def _proposed_helper_claim_key(
    name: str,
    statement: str,
    *,
    proposal_revision: int = 1,
) -> str:
    helper_name = str(name or "").strip()
    statement_key = canonical_dossier_statement_key(statement)
    revision = max(1, int(proposal_revision or 1))
    revision_key = f"proposal_revision:{revision}" if revision > 1 else ""
    return "\n".join(
        item for item in (helper_name, statement_key, revision_key) if item
    )


def _next_proposed_helper_revision(
    dossier: "ProofDossier",
    *,
    name: str,
    statement: str,
    starting_revision: int = 1,
) -> int:
    """Allocate a live proposal generation without reusing tombstone IDs."""

    graph = getattr(dossier, "proof_graph", None)
    revision = max(1, int(starting_revision or 1))
    if graph is None:
        return revision
    helper_name = str(name or "").strip()
    statement_key = canonical_dossier_statement_key(statement)
    live_revisions: List[int] = []
    for node in list(getattr(graph, "nodes", {}).values()):
        if node.kind not in {"proposed_claim", "formal_variant"}:
            continue
        if graph.is_superseded_tombstone(node):
            continue
        if helper_name and helper_name not in _proposal_node_aliases(node):
            continue
        if canonical_dossier_statement_key(node.statement) != statement_key:
            continue
        metadata = dict(getattr(node, "metadata", {}) or {})
        try:
            live_revisions.append(int(metadata.get("proposal_revision") or 0))
        except (TypeError, ValueError):
            continue
    if live_revisions:
        return max(1, max(live_revisions))
    while True:
        claim_key = _proposed_helper_claim_key(
            name,
            statement,
            proposal_revision=revision,
        )
        claim_id = graph.claim_node_id(claim_key)
        claim_node = graph.nodes.get(claim_id)
        variant_node = graph.nodes.get(
            graph.formal_variant_node_id(claim_id, statement)
        )
        if not graph.is_superseded_tombstone(
            claim_node
        ) and not graph.is_superseded_tombstone(variant_node):
            return revision
        revision += 1


def _proposal_node_name(node: Any) -> str:
    metadata = dict(getattr(node, "metadata", {}) or {})
    if str(getattr(node, "kind", "") or "") == "formal_variant":
        node_label = str(getattr(node, "name", "") or "").strip()
        variant_name = str(metadata.get("variant_name") or "").strip()
        if (
            not variant_name
            and node_label
            and not re.fullmatch(r"variant_[0-9a-f]{16}", node_label)
        ):
            variant_name = node_label
        context_name = str(
            metadata.get("proposed_helper_name")
            or metadata.get("helper_name")
            or metadata.get("claim_name")
            or ""
        ).strip()
        if variant_name and context_name and variant_name != context_name:
            return f"{context_name}\nvariant:{variant_name}"
        if variant_name:
            return variant_name
        if context_name:
            return context_name
        return str(getattr(node, "name", "") or "").strip()
    name_keys = (
        "proposed_helper_name",
        "helper_name",
        "claim_name",
        "variant_name",
    )
    for key in name_keys:
        value = str(metadata.get(key) or "").strip()
        if value:
            return value
    return str(
        getattr(node, "name", "")
    ).strip()


def _proposal_node_aliases(node: Any) -> Set[str]:
    metadata = dict(getattr(node, "metadata", {}) or {})
    if str(getattr(node, "kind", "") or "") == "formal_variant":
        helper_aliases = [
            str(metadata.get("proposed_helper_name") or "").strip(),
            str(metadata.get("helper_name") or "").strip(),
        ]
        if any(helper_aliases):
            return {item for item in helper_aliases if item}
    aliases: List[str] = []
    for key in (
        "proposed_helper_name",
        "helper_name",
        "variant_name",
        "claim_name",
    ):
        value = str(metadata.get(key) or "").strip()
        if value:
            aliases.append(value)
    node_name = str(getattr(node, "name", "") or "").strip()
    if node_name:
        aliases.append(node_name)
    return {item for item in aliases if item}


def _graph_node_is_invalidated_or_rejected(graph: ProofGraph, node: Any) -> bool:
    if node is None:
        return False
    try:
        if graph.is_superseded_tombstone(node):
            return True
    except Exception:
        pass
    metadata = dict(getattr(node, "metadata", {}) or {})
    if metadata.get("proposal_invalidated") or metadata.get("proposal_superseded"):
        return True
    return str(getattr(node, "status", "") or "") in {"rejected", "failed"}


def _mini_recursive_dependency_statement(
    graph: ProofGraph,
    dependency: str,
    *,
    pass_index: Any = None,
    ignore_node_ids: Optional[Set[str]] = None,
) -> Tuple[str, str]:
    """Resolve a planner dependency label to a live executable statement.

    Mini-recursive dependency records carry labels (``pf_decomposition``) rather
    than Lean declarations.  Labels must not become proof obligations by
    themselves; they are only routing hints back to the claim/variant nodes that
    introduced the dependency.
    """

    dep = str(dependency or "").strip()
    if not dep:
        return "", "empty"
    exact_pass = str(pass_index) if pass_index is not None else ""
    ignored = {str(node_id or "").strip() for node_id in (ignore_node_ids or set())}
    candidates: List[Tuple[int, Any]] = []
    saw_invalidated = False
    saw_label = False
    for node in list(getattr(graph, "nodes", {}).values()):
        if str(getattr(node, "kind", "") or "") not in {
            "formal_variant",
            "proposed_claim",
        }:
            continue
        if str(getattr(node, "node_id", "") or "").strip() in ignored:
            continue
        if dep not in _proposal_node_aliases(node):
            continue
        saw_label = True
        metadata = dict(getattr(node, "metadata", {}) or {})
        node_pass = str(metadata.get("pass_index")) if metadata.get("pass_index") is not None else ""
        pass_penalty = 0 if not exact_pass or node_pass == exact_pass else 10
        if _graph_node_is_invalidated_or_rejected(graph, node):
            saw_invalidated = True
            continue
        statement = str(getattr(node, "statement", "") or "").strip()
        if not graph_statement_is_executable(statement):
            continue
        kind_rank = 0 if str(getattr(node, "kind", "") or "") == "formal_variant" else 1
        candidates.append((pass_penalty + kind_rank, node))
    if candidates:
        candidates.sort(key=lambda item: item[0])
        return str(getattr(candidates[0][1], "statement", "") or "").strip(), "resolved"
    if saw_invalidated:
        return "", "invalidated"
    if saw_label:
        return "", "no_executable_statement"
    return "", "unresolved"


def _live_graph_proposal_nodes_for_helper_statement(
    graph: ProofGraph,
    *,
    name: str,
    statement: str,
) -> Tuple[Any, Any]:
    node_order = {
        getattr(node, "node_id", ""): index
        for index, node in enumerate(getattr(graph, "nodes", {}).values())
    }

    def candidate_score(node: Any) -> Tuple[int, int, int]:
        metadata = dict(getattr(node, "metadata", {}) or {})
        try:
            proposal_revision = int(metadata.get("proposal_revision") or 0)
        except (TypeError, ValueError):
            proposal_revision = 0
        return (
            proposal_revision,
            int(getattr(node, "turn_index", 0) or 0),
            int(node_order.get(getattr(node, "node_id", ""), 0)),
        )

    helper_name = str(name or "").strip()
    statement_key = canonical_dossier_statement_key(statement)
    claim_candidates: List[Any] = []
    for node in graph.nodes_by_kind("proposed_claim"):
        if graph.is_superseded_tombstone(node):
            continue
        if helper_name and helper_name not in _proposal_node_aliases(node):
            continue
        if canonical_dossier_statement_key(node.statement) != statement_key:
            continue
        claim_candidates.append(node)
    variant_candidates: List[Any] = []
    for node in graph.nodes_by_kind("formal_variant"):
        if graph.is_superseded_tombstone(node):
            continue
        if helper_name and helper_name not in _proposal_node_aliases(node):
            continue
        if canonical_dossier_statement_key(node.statement) != statement_key:
            continue
        variant_candidates.append(node)
    claim = max(claim_candidates, key=candidate_score) if claim_candidates else None
    variant = None
    for candidate in sorted(variant_candidates, key=candidate_score, reverse=True):
        claim_node_id = str((candidate.metadata or {}).get("claim_node_id") or "").strip()
        if claim is None or not claim_node_id or claim_node_id == claim.node_id:
            variant = candidate
            break
    return claim, variant


def _supersede_duplicate_live_graph_proposals_for_helper_statement(
    graph: ProofGraph,
    *,
    name: str,
    statement: str,
    active_claim_id: str = "",
    active_variant_id: str = "",
) -> None:
    helper_name = str(name or "").strip()
    statement_key = canonical_dossier_statement_key(statement)
    active_ids = {
        str(active_claim_id or "").strip(),
        str(active_variant_id or "").strip(),
    }
    active_ids.discard("")
    for node in list(getattr(graph, "nodes", {}).values()):
        if node.kind not in {"proposed_claim", "formal_variant"}:
            continue
        if node.node_id in active_ids or graph.is_superseded_tombstone(node):
            continue
        if helper_name and helper_name not in _proposal_node_aliases(node):
            continue
        if canonical_dossier_statement_key(node.statement) != statement_key:
            continue
        active_source_id = (
            str(active_claim_id or "")
            if node.kind == "proposed_claim"
            else str(active_variant_id or "")
        )
        node.metadata["duplicate_active_proposal_superseded_by"] = (
            active_claim_id if node.kind == "proposed_claim" else active_variant_id
        )
        graph._mark_node_superseded_by_source(
            node,
            source_node_id=active_source_id,
        )
        graph.record_attempt(
            node.node_id,
            phase="proposal_duplicate_generation_superseded",
            turn_index=0,
            proof="",
            verdict="proof_policy_rejected",
            error_type="proposal_superseded",
            metadata={
                "helper_name": helper_name,
                "active_claim_id": str(active_claim_id or ""),
                "active_variant_id": str(active_variant_id or ""),
            },
        )
    graph.enforce_superseded_tombstones()


def _record_or_reuse_proposed_helper_graph_nodes(
    dossier: "ProofDossier",
    *,
    name: str,
    statement: str,
    source: str,
    phase: str,
    turn_index: int,
    proposal_revision: int,
) -> Tuple[Any, Any]:
    graph = getattr(dossier, "proof_graph", None)
    if graph is None:
        return None, None
    metadata = {
        "proposed_helper_name": str(name or "").strip(),
        "proposal_revision": max(1, int(proposal_revision or 1)),
        **dossier.statement_environment_metadata(),
    }
    claim, variant = _live_graph_proposal_nodes_for_helper_statement(
        graph,
        name=name,
        statement=statement,
    )
    if claim is None:
        claim = graph.record_proposed_claim(
            name=name,
            statement=statement,
            claim_key=_proposed_helper_claim_key(
                name,
                statement,
                proposal_revision=proposal_revision,
            ),
            source=source,
            phase=phase,
            turn_index=turn_index,
            metadata=metadata,
        )
    else:
        claim.name = str(name or "").strip() or claim.name
        claim.statement = statement
        if phase:
            claim.phase = str(phase or "")
        if turn_index:
            claim.turn_index = int(turn_index or 0)
        if source:
            claim.source_hash = text_hash(source)
        claim.metadata.update(metadata)
        graph.add_edge(graph.root_node_id, claim.node_id, "proposes_claim")
    if variant is None:
        variant = graph.record_formal_variant(
            claim_node_id=claim.node_id,
            claim_name=name,
            statement=statement,
            variant_name=name,
            source=source,
            phase=phase,
            turn_index=turn_index,
            metadata=metadata,
        )
    else:
        variant.name = str(name or "").strip() or variant.name
        variant.statement = statement
        if phase:
            variant.phase = str(phase or "")
        if turn_index:
            variant.turn_index = int(turn_index or 0)
        if source:
            variant.source_hash = text_hash(source)
        variant.metadata.update(metadata)
        variant.metadata["claim_node_id"] = claim.node_id
        graph.add_edge(claim.node_id, variant.node_id, "claim_formalized_as")
    _supersede_unmatched_child_variants_for_active_claim(
        graph,
        claim_node_id=claim.node_id,
        active_statement_key=canonical_dossier_statement_key(statement),
        helper_name=name,
        superseding_node_id=variant.node_id if variant is not None else claim.node_id,
        phase="variant_superseded_by_proposed_helper",
    )
    _supersede_duplicate_live_graph_proposals_for_helper_statement(
        graph,
        name=name,
        statement=statement,
        active_claim_id=claim.node_id,
        active_variant_id=variant.node_id,
    )
    return claim, variant


@dataclass
class VerifiedHelper:
    name: str
    source: str
    source_hash: str
    phase: str
    turn_index: int
    support_names: List[str] = field(default_factory=list)
    support_source_hashes: Dict[str, str] = field(default_factory=dict)
    replay_context_names: List[str] = field(default_factory=list)
    replay_context_source_hashes: Dict[str, str] = field(default_factory=dict)
    provenance_tags: List[str] = field(default_factory=list)
    visibility_policy: str = ""
    quality_tags: List[str] = field(default_factory=list)
    open_premise_statement_keys: List[str] = field(default_factory=list)
    open_premise_statements: List[str] = field(default_factory=list)
    closed_open_premise_statements: List[str] = field(default_factory=list)
    render_policy: str = ""
    verification_environment_hash: str = ""
    contract_identity: str = ""
    contract_identity_statement_key: str = ""
    contract_identity_environment_hash: str = ""
    contract_identity_evidence_receipt: str = ""
    contract_display_statement: str = ""
    contract_binder_sorts: List[str] = field(default_factory=list)
    contract_proof_binder_types: List[str] = field(default_factory=list)


def verified_helper_bound_contract_identity(helper: Any) -> str:
    """Return structural evidence only when its durable binding is intact."""

    identity = str(getattr(helper, "contract_identity", "") or "").strip()
    statement_key = str(
        getattr(helper, "contract_identity_statement_key", "") or ""
    ).strip()
    environment_hash = str(
        getattr(helper, "contract_identity_environment_hash", "") or ""
    ).strip()
    receipt = str(
        getattr(helper, "contract_identity_evidence_receipt", "") or ""
    ).strip()
    source_statement_key = canonical_dossier_statement_key(
        helper_decl_statement(str(getattr(helper, "source", "") or ""))
    )
    verification_environment_hash = str(
        getattr(helper, "verification_environment_hash", "") or ""
    ).strip()
    if (
        not source_statement_key
        or statement_key != source_statement_key
        or environment_hash != verification_environment_hash
        or not lean_contract_evidence_receipt_matches(
            receipt,
            identity=identity,
            statement_key=statement_key,
            environment_hash=environment_hash,
        )
    ):
        return ""
    return identity


def verified_helper_surface_statement_changed(existing: Any, incoming: Any) -> bool:
    """Return whether two helper declarations have different propositions."""

    existing_statement = " ".join(
        str(
            helper_decl_statement(str(getattr(existing, "source", "") or ""))
            or ""
        ).split()
    )
    incoming_statement = " ".join(
        str(
            helper_decl_statement(str(getattr(incoming, "source", "") or ""))
            or ""
        ).split()
    )
    if existing_statement and incoming_statement:
        return existing_statement != incoming_statement
    return str(getattr(existing, "source", "") or "").strip() != str(
        getattr(incoming, "source", "") or ""
    ).strip()


def verified_helper_semantic_statement_changed(existing: Any, incoming: Any) -> bool:
    """Return whether replacement evidence changes the proved proposition.

    Surface syntax is insufficient across Lean environments: identical text can
    elaborate to different expressions, while alpha-renaming and notation can
    make identical expressions look different. Prefer Lean's full-expression
    identity whenever either side carries verified contract evidence.
    """

    existing_identity = verified_helper_bound_contract_identity(existing)
    incoming_identity = verified_helper_bound_contract_identity(incoming)
    if existing_identity or incoming_identity:
        if not existing_identity or not incoming_identity:
            return True
        existing_parts = parse_lean_contract_identity(existing_identity)
        incoming_parts = parse_lean_contract_identity(incoming_identity)
        if existing_parts is None or incoming_parts is None:
            return True
        return existing_parts[0] != incoming_parts[0]

    # Without receipt-bound Lean evidence, syntax normalization is not an
    # authority boundary. Preserve the prior fail-closed surface decision.
    return verified_helper_surface_statement_changed(existing, incoming)


@dataclass
class VerifiedHelperProgressDelta:
    """Run-local ledger entry separating theory value from parent impact."""

    helper_name: str
    statement_key: str = ""
    canonical_helper_name: str = ""
    theory_progress: bool = False
    resolved_claim_node_ids: List[str] = field(default_factory=list)
    resolved_variant_node_ids: List[str] = field(default_factory=list)
    resolved_obligation_node_ids: List[str] = field(default_factory=list)

    @property
    def parent_progress(self) -> bool:
        return bool(
            self.resolved_claim_node_ids
            or self.resolved_variant_node_ids
            or self.resolved_obligation_node_ids
        )

    @property
    def parent_progress_edge_count(self) -> int:
        return (
            len(self.resolved_claim_node_ids)
            + len(self.resolved_variant_node_ids)
            + len(self.resolved_obligation_node_ids)
        )


def _merge_verified_helper_progress_delta(
    dossier: Any,
    helper: "VerifiedHelper",
    *,
    statement_key: str = "",
    resolved_claim_node_ids: Optional[Iterable[str]] = None,
    resolved_variant_node_ids: Optional[Iterable[str]] = None,
    resolved_obligation_node_ids: Optional[Iterable[str]] = None,
) -> None:
    """Merge newly resolved graph impact into the helper progress ledger."""

    name = str(getattr(helper, "name", "") or "").strip()
    if not name:
        return
    deltas = getattr(dossier, "verified_helper_progress_deltas", None)
    if not isinstance(deltas, dict):
        deltas = {}
        setattr(dossier, "verified_helper_progress_deltas", deltas)
    existing = _coerce_verified_helper_progress_delta(deltas.get(name))
    aliases = getattr(dossier, "verified_helper_statement_aliases", {}) or {}
    canonical_helper_name = str(
        aliases.get(name)
        or getattr(existing, "canonical_helper_name", "")
        or name
    ).strip()
    delta = existing or VerifiedHelperProgressDelta(
        helper_name=name,
        statement_key=str(statement_key or "").strip(),
        canonical_helper_name=canonical_helper_name,
    )
    delta.helper_name = name
    if statement_key:
        delta.statement_key = str(statement_key or "").strip()
    if canonical_helper_name:
        delta.canonical_helper_name = canonical_helper_name
    helper_is_generic = verified_helper_admission_quality(helper).generic_novelty
    delta.theory_progress = bool(
        helper_is_generic
        and (
            delta.theory_progress
            or (
                canonical_helper_name == name
                and _verified_helper_counts_for_theory_progress(dossier, helper)
            )
        )
    )

    if not helper_is_generic:
        delta.resolved_claim_node_ids.clear()
        delta.resolved_variant_node_ids.clear()
        delta.resolved_obligation_node_ids.clear()
        deltas[name] = delta
        return

    for target, source in (
        (delta.resolved_claim_node_ids, resolved_claim_node_ids),
        (delta.resolved_variant_node_ids, resolved_variant_node_ids),
        (delta.resolved_obligation_node_ids, resolved_obligation_node_ids),
    ):
        for raw_node_id in list(source or []):
            node_id = str(raw_node_id or "").strip()
            if node_id and node_id not in target:
                target.append(node_id)
    deltas[name] = delta


@dataclass
class ProposedHelper:
    """A helper the prover proposed but did not (yet) verify with Lean.

    Banked from ``no_proof_extracted`` (and policy-rejected) turns so
    that downstream phases — most importantly the recursive planner —
    can seed claims from the prover's own decomposition signal instead
    of asking the LLM to re-invent helpers it already named.

    Idempotent on name: re-proposing the same helper updates the
    statement / source / phase / turn_index to the freshest value.
    """

    name: str
    statement: str
    source: str
    source_hash: str
    phase: str
    turn_index: int
    proposal_revision: int = 1
    statement_environment_hash: str = ""


@dataclass
class ProofAttemptRecord:
    phase: str
    turn_index: int
    proof_hash: str
    helper_names: List[str]
    verdict: str
    error_type: str = ""


_MAX_PROOF_ATTEMPT_RECORDS = 256


@dataclass
class ScratchRecord:
    turn_index: int
    tool_call_index: int
    ok: bool
    summary: str
    code_hash: str
    normalized_code: str = ""
    goal_hash: str = ""
    goal_key: str = ""
    referenced_names: List[str] = field(default_factory=list)
    source_label: str = "try_lean"


def _bounded_scratch_records(
    records: Sequence[ScratchRecord],
    *,
    max_records: int = _MAX_DOSSIER_SCRATCH_RECORDS,
    max_per_goal: int = _MAX_DOSSIER_SCRATCH_RECORDS_PER_GOAL,
    max_failed_per_goal: int = _MAX_DOSSIER_FAILED_SCRATCH_RECORDS_PER_GOAL,
) -> List[ScratchRecord]:
    """Retain recent scratch with bounded, goal-diverse persistence.

    First reserve recent failed routes for every goal, then preserve each
    goal's newest observation and fill remaining capacity by recency. This
    prevents a burst of successful probes from erasing all durable failed-route
    memory before recursive handoff. Returned records remain chronological.
    """

    indexed = list(enumerate(records or ()))
    limit = max(0, int(max_records or 0))
    per_goal_limit = max(1, int(max_per_goal or 1))
    failed_per_goal_limit = max(
        1,
        min(per_goal_limit, int(max_failed_per_goal or 1)),
    )
    if limit <= 0:
        return []
    selected: Set[int] = set()
    goal_counts: Dict[str, int] = {}

    canonical_keys_by_legacy_hash: Dict[str, Set[str]] = {}
    for _index, item in indexed:
        goal_hash = str(getattr(item, "goal_hash", "") or "").strip()
        goal_key = str(getattr(item, "goal_key", "") or "").strip()
        if goal_hash and goal_key:
            canonical_keys_by_legacy_hash.setdefault(goal_hash, set()).add(
                goal_key
            )
    unique_canonical_key_by_legacy_hash = {
        goal_hash: next(iter(goal_keys))
        for goal_hash, goal_keys in canonical_keys_by_legacy_hash.items()
        if len(goal_keys) == 1
    }

    def goal_identity(item: ScratchRecord) -> str:
        goal_key = str(getattr(item, "goal_key", "") or "").strip()
        goal_hash = str(getattr(item, "goal_hash", "") or "").strip()
        if goal_key:
            return f"canonical:{goal_key}"
        bridged_key = unique_canonical_key_by_legacy_hash.get(goal_hash, "")
        if bridged_key:
            return f"canonical:{bridged_key}"
        if goal_hash:
            return f"legacy_hash:{goal_hash}"
        return "__unscoped__"

    failed_candidates_by_goal: Dict[str, List[int]] = {}
    for index, item in reversed(indexed):
        if bool(getattr(item, "ok", False)):
            continue
        goal_key = goal_identity(item)
        candidates = failed_candidates_by_goal.setdefault(goal_key, [])
        if len(candidates) < failed_per_goal_limit:
            candidates.append(index)
    primary_failed_candidates = sorted(
        (
            candidates[0]
            for candidates in failed_candidates_by_goal.values()
            if candidates
        ),
        reverse=True,
    )
    failed_counts: Dict[str, int] = {}
    for index in primary_failed_candidates[:limit]:
        goal_key = goal_identity(indexed[index][1])
        selected.add(index)
        goal_counts[goal_key] = int(goal_counts.get(goal_key, 0) or 0) + 1
        failed_counts[goal_key] = int(failed_counts.get(goal_key, 0) or 0) + 1

    # Preserve one newest observation from every otherwise-unrepresented goal
    # before spending capacity on extra routes from already-covered goals.
    for index, item in reversed(indexed):
        if len(selected) >= limit:
            break
        goal_key = goal_identity(item)
        if int(goal_counts.get(goal_key, 0) or 0) > 0:
            continue
        selected.add(index)
        goal_counts[goal_key] = 1
        if not bool(getattr(item, "ok", False)):
            failed_counts[goal_key] = 1

    extra_failed_candidates = sorted(
        (
            index
            for candidates in failed_candidates_by_goal.values()
            for index in candidates[1:]
        ),
        reverse=True,
    )
    for index in extra_failed_candidates:
        if len(selected) >= limit:
            break
        if index in selected:
            continue
        item = indexed[index][1]
        goal_key = goal_identity(item)
        if int(goal_counts.get(goal_key, 0) or 0) >= per_goal_limit:
            continue
        if int(failed_counts.get(goal_key, 0) or 0) >= failed_per_goal_limit:
            continue
        selected.add(index)
        goal_counts[goal_key] = int(goal_counts.get(goal_key, 0) or 0) + 1
        failed_counts[goal_key] = int(failed_counts.get(goal_key, 0) or 0) + 1

    if len(selected) < limit:
        for index, item in reversed(indexed):
            if index in selected:
                continue
            goal_key = goal_identity(item)
            if int(goal_counts.get(goal_key, 0) or 0) >= per_goal_limit:
                continue
            selected.add(index)
            goal_counts[goal_key] = int(goal_counts.get(goal_key, 0) or 0) + 1
            if len(selected) >= limit:
                break

    return [item for index, item in indexed if index in selected]


@dataclass
class AcceptedProofStub:
    turn_index: int
    tool_call_index: int
    goal_hash: str
    preamble_hash: str
    context_hash: str
    code_hash: str
    normalized_code: str


@dataclass
class DeclApplicationRecord:
    turn_index: int
    tool_call_index: int
    decl_name: str
    statement_hash: str
    applicable: bool
    closed: bool
    remaining_goal_count: int
    proof_stub_hash: str = ""
    error_kind: str = ""
    statement_preview: str = ""
    proof_stub: str = ""
    remaining_goals_preview: List[str] = field(default_factory=list)
    error_text: str = ""
    error_text_is_lean_diagnostic: bool = True
    decl_type: str = ""


@dataclass
class ProofDossier:
    """Compact proof graph for one mini-prover run.

    This is intentionally modest: it tracks durable Lean-checked artifacts and
    enough failed-attempt metadata to guide the next turn.  It is not a full
    replacement for a recursive prover yet, but it gives the mini prover the
    missing source of truth needed by helper salvage and scratch tooling.
    """

    theorem_name: str
    root_statement: str
    problem_text: str = ""
    # Cache ownership is intentionally distinct from ``theorem_name``.  A
    # recursive child needs its own theorem name for Lean and graph semantics,
    # but any helper that is ultimately accepted by the root must be seeded on
    # the next run under the root theorem's cache namespace.
    cache_owner_theorem_name: str = ""
    # Only the dossier that owns durable acceptance may publish to the
    # persistent cache.  Transient recursive child dossiers are merged through
    # that owner first, so withheld/filtered child helpers cannot leak into a
    # later run merely because they happened to typecheck locally.
    proof_cache_publish_enabled: bool = True
    # PutnamBench uses ``*_solution`` as a hidden official-answer channel.
    # General theorem projects may legitimately use that suffix, so the
    # adapter owns this policy instead of the identifier spelling.
    suppress_solution_placeholders: bool = True
    verified_helpers: Dict[str, VerifiedHelper] = field(default_factory=dict)
    superseded_verified_helper_hashes: Dict[str, List[str]] = field(
        default_factory=dict
    )
    verified_helper_source_hash_history: Dict[str, List[str]] = field(
        default_factory=dict
    )
    # Monotone count of verified-helper evictions.  The helper SET alone cannot
    # distinguish "never had this helper" from "had it and a repair removed
    # it": both hash identically, so a progress guard keyed on durable state
    # reads a post-repair session as one that never moved.  This only ever
    # increases, so it separates regression from stasis.
    verified_helper_eviction_generation: int = 0
    # Fix 1 (2026-05-22): when a helper with the same canonical statement
    # arrives under a fresh name, alias it to the original instead of minting
    # a new verified record. Maps requested_name → canonical verified name.
    # Drives the "5 duplicate Icc → range" collapse seen in putnam_1962_a5.
    verified_helper_statement_aliases: Dict[str, str] = field(default_factory=dict)
    verified_helper_progress_deltas: Dict[str, VerifiedHelperProgressDelta] = field(
        default_factory=dict
    )
    # Append-only cross-subsystem proof-path events. The proof graph remains
    # authoritative; this ledger makes strategy/route/claim/attempt/fact
    # lineage queryable without reconstructing it from unrelated identifiers.
    proof_lineage_events: List[Dict[str, Any]] = field(default_factory=list)
    proof_lineage_event_ids: Set[str] = field(default_factory=set)
    # Content-owning, descriptive lifecycle aggregates for mathematical
    # strategies. Proof authority remains exclusively in Lean/certificates and
    # the proof graph; these records conserve intent and attempt evolution.
    proof_ideas: Dict[str, ProofIdeaRecord] = field(default_factory=dict)
    # Singleton inference is safe only for an explicitly isolated recursive
    # child. Root/controller dossiers may temporarily contain one idea while
    # receiving unrelated tool turns, so cardinality alone is not lineage.
    proof_idea_singleton_child_scope: bool = False
    # Structural accepted-fact registry and cumulative retirement receipts.
    # A receipt may gain newly projected graph nodes after initial acceptance.
    semantic_fact_registry: Dict[str, Dict[str, Any]] = field(default_factory=dict)
    # Empirical scheduler calibration, keyed by action id. Values are compact
    # cumulative counters (attempts, seconds, root-relevant progress events).
    action_value_observations: Dict[str, Dict[str, float]] = field(
        default_factory=dict
    )
    proposed_helpers: Dict[str, ProposedHelper] = field(default_factory=dict)
    attempts: List[ProofAttemptRecord] = field(default_factory=list)
    scratch: List[ScratchRecord] = field(default_factory=list)
    accepted_proof_stubs: List[AcceptedProofStub] = field(default_factory=list)
    tool_metrics: Dict[str, int] = field(default_factory=dict)
    decl_applications: List[DeclApplicationRecord] = field(default_factory=list)
    mini_recursive_runs: List[Dict[str, Any]] = field(default_factory=list)
    mini_recursive_claim_helper_bindings: Dict[str, Dict[str, Any]] = field(
        default_factory=dict
    )
    mini_recursive_invalidated_statement_reasons: Dict[str, str] = field(
        default_factory=dict
    )
    # Typed provenance is required before an invalidation may cross a branch
    # or checkpoint trust boundary.  Free-form reason strings remain useful
    # within one live run but are never durable mathematical evidence.
    mini_recursive_invalidation_provenance: Dict[str, Dict[str, Any]] = field(
        default_factory=dict
    )
    # Process-local mathematical authority. Entries are admitted only from a
    # complete, integrity-checked report/certificate pair and bind exact source
    # bytes plus (when available) the elaborated Lean expression in one target
    # environment. This map is serialized for audit only and deliberately
    # cleared on restore until the certificate is freshly replayed.
    mini_authoritative_negations: Dict[str, Dict[str, Any]] = field(
        default_factory=dict
    )
    # Append-only falsification evidence.  Heuristic findings live here for
    # observability/resumption, but only axiom-audited full-negation
    # certificates are allowed to populate the invalidation map below.
    mini_falsification_ledger: List[Dict[str, Any]] = field(default_factory=list)
    # lossy canonical shortlist -> exact/bound target identity -> engine
    # cursor. Canonical statement keys never own progress directly.
    mini_falsification_cursors: Dict[str, Dict[str, Any]] = field(
        default_factory=dict
    )
    root_disproof_certificate: Optional[Dict[str, Any]] = None
    # Persisted certificates are replay candidates, never restored authority.
    mini_falsification_pending_certificates: List[Dict[str, Any]] = field(
        default_factory=list
    )
    # Definitive replay rejection is scoped to the exact certificate,
    # verifier environment, and falsification policy.  It suppresses repeated
    # replay work only; it is never mathematical evidence or authority.
    mini_falsification_certificate_replay_dispositions: Dict[
        str, Dict[str, Any]
    ] = field(default_factory=dict)
    # Durable identity of independently replayed/audited certificates that
    # conflicted with existing positive Lean authority.  This is terminal
    # conflict evidence, never disproof authority by itself.
    mini_falsification_trust_boundary_conflict_certificate_hashes: Set[str] = field(
        default_factory=set
    )
    mini_recursive_exhausted_claim_keys: Set[str] = field(default_factory=set)
    opaque_mode: bool = True
    allow_official_answer_visibility: bool = False
    official_answer_payload_present: Optional[bool] = None
    active_root_targets: List[Dict[str, Any]] = field(default_factory=list)
    active_root_classification_preamble_hash: str = ""
    parallel_sample_proof_states: List[Dict[str, Any]] = field(default_factory=list)
    parallel_sample_failures: List[Dict[str, Any]] = field(default_factory=list)
    final_proof: Optional[str] = None
    final_proof_hash: Optional[str] = None
    final_replay_helpers: List[str] = field(default_factory=list)
    root_proof_certificate: Optional[Dict[str, Any]] = None
    # Process-local receipt minted only after canonical root finalization has
    # completed every replay, route, deadline, and persistence gate. Public
    # report records deliberately cannot restore this authority.
    _root_proof_finalization_receipts: Set[str] = field(
        default_factory=set,
        repr=False,
    )
    proof_graph: Optional[ProofGraph] = None
    graph_execution_projection_mode: str = "shadow"
    graph_execution_project_environment_hash: str = ""
    current_lean_environment_hash: str = ""
    # child environment hash -> transitive hashes whose declarations remain
    # available in that child.  Direction matters: a fact checked in an
    # ancestor is valid after a monotone extension, but not conversely.
    lean_environment_ancestor_hashes: Dict[str, List[str]] = field(
        default_factory=dict
    )
    # environment hash -> sorted digests of that environment's declaration
    # lines.  ``extends`` is a caller assertion that the hash pair cannot
    # check; recorded content lets the lattice refuse an edge whose claimed
    # extension is provably a shrink.  Absent content keeps the legacy
    # assertion path, so this narrows behaviour only where it can prove harm.
    lean_environment_content_digests: Dict[str, List[str]] = field(
        default_factory=dict
    )

    def __post_init__(self) -> None:
        self.suppress_solution_placeholders = (
            effective_solution_placeholder_suppression(
                suppress_solution_placeholders=(
                    self.suppress_solution_placeholders
                ),
                opaque_mode=self.opaque_mode,
                allow_official_answer_visibility=(
                    self.allow_official_answer_visibility
                ),
                official_answer_payload_present=(
                    self.official_answer_payload_present
                ),
            )
        )
        projection_mode = str(
            self.graph_execution_projection_mode or ""
        ).strip().lower()
        if projection_mode not in {"off", "shadow"}:
            raise ValueError(
                "graph_execution_projection_mode must be one of: off, shadow"
            )
        self.graph_execution_projection_mode = projection_mode
        self._compact_attempt_history()
        if not str(self.cache_owner_theorem_name or "").strip():
            self.cache_owner_theorem_name = str(self.theorem_name or "").strip()
        if self.proof_graph is None:
            self.proof_graph = ProofGraph(
                theorem_name=self.theorem_name,
                root_statement=self.root_statement,
            )
        else:
            self.proof_graph.theorem_name = self.theorem_name
            self.proof_graph.ensure_root(self.root_statement)
        self.lean_environment_ancestor_hashes = {
            str(child or "").strip(): list(
                dict.fromkeys(
                    str(ancestor or "").strip()
                    for ancestor in list(ancestors or [])
                    if str(ancestor or "").strip()
                )
            )
            for child, ancestors in dict(
                self.lean_environment_ancestor_hashes or {}
            ).items()
            if str(child or "").strip()
        }
        self._sanitize_lean_environment_ancestor_hashes()
        self._refresh_all_graph_node_environment_ancestry()
        if self.active_root_targets:
            self.record_active_root_targets(self.active_root_targets)
        ready_before = self._ready_route_ids()
        self._sync_legacy_helpers_to_graph()
        self._sync_proposed_helpers_to_graph()
        self.reconcile_verified_facts(
            trigger="dossier_init",
            ready_before=ready_before,
        )

    @staticmethod
    def _ancestors_from_environment_map(
        environment_hash: str,
        ancestor_map: Mapping[str, Sequence[str]],
    ) -> List[str]:
        """Transitive ancestors from one map; cycle-safe via visited set."""

        child = str(environment_hash or "").strip()
        if not child:
            return []
        ordered: List[str] = []
        pending = [
            str(item or "").strip()
            for item in list(ancestor_map.get(child, []) or [])
            if str(item or "").strip()
        ]
        while pending:
            ancestor = str(pending.pop(0) or "").strip()
            if not ancestor or ancestor == child or ancestor in ordered:
                continue
            ordered.append(ancestor)
            pending.extend(
                str(item or "").strip()
                for item in list(ancestor_map.get(ancestor, []) or [])
                if str(item or "").strip()
            )
        return ordered

    def _sanitize_lean_environment_ancestor_hashes(self) -> None:
        """Drop self-loops and reverse edges that would invert the lattice."""

        dirty = {
            str(child or "").strip(): list(
                dict.fromkeys(
                    str(ancestor or "").strip()
                    for ancestor in list(ancestors or [])
                    if str(ancestor or "").strip()
                )
            )
            for child, ancestors in dict(
                self.lean_environment_ancestor_hashes or {}
            ).items()
            if str(child or "").strip()
        }
        clean: Dict[str, List[str]] = {}
        for child, ancestors in dirty.items():
            kept: List[str] = []
            for ancestor in ancestors:
                if not ancestor or ancestor == child:
                    continue
                # Refuse edges that make `child` an ancestor of `ancestor`
                # (cycle / direction inversion).
                if child in self._ancestors_from_environment_map(
                    ancestor, dirty
                ):
                    continue
                kept.append(ancestor)
            if kept:
                clean[child] = kept
        self.lean_environment_ancestor_hashes = clean

    def lean_environment_ancestors(
        self,
        environment_hash: str = "",
    ) -> List[str]:
        """Return the durable transitive ancestors of one Lean environment."""

        child = str(
            environment_hash or self.current_lean_environment_hash or ""
        ).strip()
        return self._ancestors_from_environment_map(
            child,
            self.lean_environment_ancestor_hashes,
        )

    def lean_environment_is_compatible(
        self,
        evidence_environment_hash: str,
        target_environment_hash: str = "",
        *,
        target_ancestor_hashes: Optional[Sequence[str]] = None,
    ) -> bool:
        """Whether evidence remains valid in the target Lean environment.

        This compatibility relation is used for import/preflight decisions.
        Fact retirement is deliberately stricter and requires exact equality.
        """

        evidence = str(evidence_environment_hash or "").strip()
        target = str(
            target_environment_hash or self.current_lean_environment_hash or ""
        ).strip()
        if not target:
            # No stamped target context: only blank/blank remains compatible for
            # pre-receipt fixtures. Stamped evidence must not retire unstamped
            # targets through this fail-open carve-out.
            return not evidence
        if not evidence:
            return False
        if evidence == target:
            return True
        ancestors = {
            str(item or "").strip()
            for item in (
                *list(target_ancestor_hashes or []),
                *self.lean_environment_ancestors(target),
            )
            if str(item or "").strip()
        }
        if evidence not in ancestors:
            return False
        # Defense in depth: a corrupt/cyclic map must not admit the converse
        # lattice direction (child evidence retiring an ancestor target).
        if target in self.lean_environment_ancestors(evidence):
            return False
        return True

    def statement_environment_metadata(self) -> Dict[str, Any]:
        """Metadata needed to interpret a graph statement after extensions."""

        environment_hash = str(self.current_lean_environment_hash or "").strip()
        return {
            "statement_environment_hash": environment_hash,
            "statement_environment_ancestor_hashes": (
                self.lean_environment_ancestors(environment_hash)
                if environment_hash
                else []
            ),
        }

    def _refresh_graph_nodes_for_environment(
        self,
        environment_hash: str,
    ) -> None:
        """Keep frozen node ancestor lists aligned with the live dossier map.

        Only the ancestor list is refreshed. Re-stamping through
        ``stamp_graph_node_environment`` would remint or strip contract-identity
        receipts and recreate the dossier/graph dual-authority divergence this
        refresh exists to close.
        """

        environment = str(environment_hash or "").strip()
        if not environment or self.proof_graph is None:
            return
        ancestor_hashes = self.lean_environment_ancestors(environment)
        for node in self.proof_graph.nodes.values():
            metadata = getattr(node, "metadata", None)
            if not isinstance(metadata, dict):
                continue
            if str(metadata.get("statement_environment_hash") or "").strip() != (
                environment
            ):
                continue
            frozen = [
                str(item or "").strip()
                for item in list(
                    metadata.get("statement_environment_ancestor_hashes") or []
                )
                if str(item or "").strip()
            ]
            if frozen == ancestor_hashes:
                continue
            metadata["statement_environment_ancestor_hashes"] = list(
                ancestor_hashes
            )
            metadata["statement_environment_stamp_source"] = (
                "ancestor_map_refresh"
            )

    def _refresh_all_graph_node_environment_ancestry(self) -> None:
        """Rebind every frozen graph ancestry stamp to the sanitized map."""

        if self.proof_graph is None:
            return
        environments = {
            str(metadata.get("statement_environment_hash") or "").strip()
            for node in self.proof_graph.nodes.values()
            for metadata in [getattr(node, "metadata", None)]
            if isinstance(metadata, dict)
            and str(metadata.get("statement_environment_hash") or "").strip()
        }
        for environment in sorted(environments):
            self._refresh_graph_nodes_for_environment(environment)

    @staticmethod
    def _lean_environment_content_digest(source_text: str) -> List[str]:
        """Return order-independent digests of an environment's declaration lines.

        Declaration order is not semantic in a Lean preamble, so the digest is
        a sorted line multiset rather than a hash of the whole text.  That lets
        a permutation compare equal while a dropped declaration does not.
        """

        lines = {
            line.strip()
            for line in str(source_text or "").splitlines()
            if line.strip()
        }
        # A set, not a multiset: the subset comparison below is set-based, and
        # a Lean preamble cannot declare the same line twice and still compile.
        # Storing a multiset would promise an ordering the check never honours.
        return sorted(text_hash(line) for line in lines)

    def _environment_content_omits_parent(self, child: str, parent: str) -> bool:
        """Whether recorded content proves ``child`` drops ``parent`` declarations."""

        child_digest = self.lean_environment_content_digests.get(child)
        parent_digest = self.lean_environment_content_digests.get(parent)
        if not child_digest or not parent_digest:
            # Unknown content is not evidence of a shrink.  Fail open here so
            # legacy callers keep the extension semantics they were written
            # against; only a proven shrink narrows behaviour.
            return False
        return not set(parent_digest).issubset(set(child_digest))

    def _accept_environment_ancestor_edge(
        self,
        child: str,
        parent: str,
        *,
        previous_environment_hash: str = "",
    ) -> bool:
        """Whether recording parent as an ancestor of child preserves the lattice."""

        child_hash = str(child or "").strip()
        parent_hash = str(parent or "").strip()
        previous = str(previous_environment_hash or "").strip()
        if not child_hash or not parent_hash or child_hash == parent_hash:
            return False
        if child_hash in self.lean_environment_ancestors(parent_hash):
            return False
        if self._environment_content_omits_parent(child_hash, parent_hash):
            # The caller asserted an extension, but the recorded declaration
            # sets prove the parent's declarations are not all present in the
            # child.  Accepting the edge would let evidence checked in the
            # larger environment retire targets in the smaller one, where its
            # proof cannot replay.
            return False
        existing = list(
            self.lean_environment_ancestor_hashes.get(child_hash, []) or []
        )
        if (
            existing
            and parent_hash not in existing
            and parent_hash != previous
        ):
            # Child already has a monotone history; refuse silent expansion
            # from an unrelated parent that is not the environment being left.
            return False
        return True

    def record_lean_environment(
        self,
        environment_hash: str,
        *,
        extends_environment_hash: str = "",
        environment_source_text: str = "",
    ) -> None:
        """Select an environment and durably record a monotone extension.

        ``environment_source_text`` is the rendered preamble the hash stands
        for.  Supplying it lets the ancestry lattice reject an ``extends``
        claim that the declaration sets prove to be a shrink.
        """

        child = str(environment_hash or "").strip()
        parent = str(extends_environment_hash or "").strip()
        previous = str(self.current_lean_environment_hash or "").strip()
        if child and str(environment_source_text or "").strip():
            # Record before adjudicating the edge so the check can see this
            # environment's own declarations.
            self.lean_environment_content_digests[child] = (
                self._lean_environment_content_digest(environment_source_text)
            )
        ancestry_changed = False
        if child and parent and child != parent:
            if not self.lean_environment_content_digests.get(parent):
                # The monotonicity check needs BOTH sides' declarations, so an
                # edge onto a parent with no recorded content is accepted
                # unverified.  This is the durable-resume case: a checkpoint
                # written before content recording existed carries ancestry but
                # no digests, and the preamble text those hashes stood for is
                # gone, so it cannot be re-derived.  A session self-heals going
                # forward as new environments are stamped; count the
                # unverifiable edges so the residual is visible rather than
                # silent.
                self.increment_tool_metric(
                    "mini_lean_environment_unverified_extension",
                    1,
                )
            if self._accept_environment_ancestor_edge(
                child,
                parent,
                previous_environment_hash=previous,
            ):
                ancestors = list(
                    self.lean_environment_ancestor_hashes.get(child, []) or []
                )
                before = list(ancestors)
                for ancestor in (
                    parent,
                    *self.lean_environment_ancestors(parent),
                ):
                    if (
                        ancestor
                        and ancestor != child
                        and ancestor not in ancestors
                        and child
                        not in self.lean_environment_ancestors(ancestor)
                    ):
                        ancestors.append(ancestor)
                if ancestors != before:
                    self.lean_environment_ancestor_hashes[child] = ancestors
                    ancestry_changed = True
        self.current_lean_environment_hash = child
        if ancestry_changed:
            self._refresh_graph_nodes_for_environment(child)

    @staticmethod
    def _lineage_event_occurrence_key(
        event_type: str,
        details: Mapping[str, Any],
    ) -> str:
        """Return a stable occurrence discriminator for lineage event identity."""

        payload = dict(details or {})
        attempt_id = str(payload.get("proof_attempt_id") or "").strip()
        if attempt_id:
            return f"attempt:{attempt_id}"
        resolved = [
            str(item or "").strip()
            for item in list(payload.get("resolved_node_ids") or [])
            if str(item or "").strip()
        ]
        if resolved:
            return stable_identity(
                "lineage-resolved-set",
                event_type,
                *sorted(resolved),
            )
        return ""

    def record_proof_lineage_event(
        self,
        *,
        event_type: str,
        envelope: ProofLineageEnvelope,
        phase: str = "",
        verdict: str = "",
        evidence_hash: str = "",
        details: Optional[Mapping[str, Any]] = None,
    ) -> str:
        """Append one idempotent proof-lineage event."""

        detail_payload = dict(details or {})
        event_id = lineage_event_identity(
            event_type=event_type,
            envelope=envelope,
            phase=phase,
            verdict=verdict,
            evidence_hash=evidence_hash,
            occurrence_key=self._lineage_event_occurrence_key(
                str(event_type or ""),
                detail_payload,
            ),
        )
        if event_id in self.proof_lineage_event_ids:
            return event_id
        self.proof_lineage_event_ids.add(event_id)
        self.proof_lineage_events.append(
            {
                "schema_version": 1,
                "event_id": event_id,
                "event_type": str(event_type or "").strip(),
                "phase": str(phase or "").strip(),
                "verdict": str(verdict or "").strip(),
                "evidence_hash": str(evidence_hash or "").strip(),
                "proof_lineage": envelope.to_record(),
                "details": copy.deepcopy(detail_payload),
            }
        )
        return event_id

    def upsert_proof_idea(self, record: ProofIdeaRecord) -> ProofIdeaRecord:
        """Merge one descriptive strategy lifecycle fragment idempotently."""

        if not isinstance(record, ProofIdeaRecord):
            raise TypeError("proof idea upsert requires ProofIdeaRecord")
        existing = self.proof_ideas.get(record.proof_idea_id)
        merged = record if existing is None else existing.merged(record)
        self.proof_ideas[record.proof_idea_id] = merged
        return merged

    def register_proof_idea_consumer(
        self,
        *,
        proof_idea_id: str,
        route_id: str,
        claim_id: str = "",
        statement_identity: str = "",
        branch_id: str = "",
        branch_source: str = "mini_prover",
    ) -> str:
        """Register one derived graph route as a lifecycle consumer.

        ``claim_id`` in a cognition binding names the conserved planner claim
        intent.  It is not the ID of a later executable graph occurrence (that
        coordinate belongs in ``graph_node_ids``).  Derived routes are often
        created after a claim has been retargeted or coalesced, so resolve the
        canonical intent by exact claim ID first and then by the structural
        statement identity.  Ambiguous or unowned occurrences remain
        fail-closed.

        The aggregate replacement and route metadata update are synchronous
        and contain no await boundary, so work-frontier projection cannot
        observe a newly stamped route without its matching consumer record.
        """

        idea_id = str(proof_idea_id or "").strip()
        consumer_route_id = str(route_id or "").strip()
        requested_claim_id = str(claim_id or "").strip()
        requested_statement_identity = str(statement_identity or "").strip()
        consumer_branch_id = str(branch_id or "").strip()
        if not idea_id or not consumer_route_id:
            return ""
        idea = self.proof_ideas.get(idea_id)
        graph = self.proof_graph
        route = (
            graph.nodes.get(consumer_route_id)
            if graph is not None
            else None
        )
        if (
            not isinstance(idea, ProofIdeaRecord)
            or route is None
            or str(getattr(route, "kind", "") or "") != "strategy_route"
        ):
            return ""
        route_metadata = (
            route.metadata if isinstance(route.metadata, dict) else {}
        )
        consumer_branch_id = str(
            consumer_branch_id or route_metadata.get("branch_id") or ""
        ).strip()
        route_idea_id = str(route_metadata.get("proof_idea_id") or "").strip()
        if route_idea_id and route_idea_id != idea_id:
            return ""
        idea_branch_ids = tuple(
            dict.fromkeys(
                item.branch_id
                for item in idea.branch_provenance
                if str(item.branch_id or "").strip()
            )
        )
        if not consumer_branch_id and len(idea_branch_ids) == 1:
            consumer_branch_id = idea_branch_ids[0]
        if len(idea_branch_ids) > 1 and not consumer_branch_id:
            return ""
        if consumer_branch_id and consumer_branch_id not in idea_branch_ids:
            # A genuinely new branch must be explicit at the producer; this
            # registration boundary may recover historical occurrences but
            # must not invent branch ownership from a route/claim match.
            return ""

        exact_claim_matches = [
            intent
            for intent in idea.claim_intents
            if requested_claim_id and intent.claim_id == requested_claim_id
        ]
        statement_matches = [
            intent
            for intent in idea.claim_intents
            if requested_statement_identity
            and requested_statement_identity
            in {
                intent.statement_identity,
                *intent.alternative_statement_identities,
            }
        ]
        matches = exact_claim_matches or statement_matches
        if len(matches) != 1:
            return ""
        matched_intent = matches[0]
        if (
            requested_statement_identity
            and requested_statement_identity
            not in {
                matched_intent.statement_identity,
                *matched_intent.alternative_statement_identities,
            }
        ):
            return ""

        updated_intents = tuple(
            replace(
                intent,
                consumer_ids=tuple(
                    dict.fromkeys((*intent.consumer_ids, consumer_route_id))
                ),
            )
            if intent.claim_id == matched_intent.claim_id
            else intent
            for intent in idea.claim_intents
        )
        branches = idea.branch_provenance
        if consumer_branch_id and consumer_branch_id not in {
            item.branch_id for item in branches
        }:
            branches = branches + (
                ProofIdeaBranchProvenance(
                    branch_id=consumer_branch_id,
                    source=str(branch_source or "mini_prover"),
                ),
            )
        updated_idea = replace(
            idea,
            consumer_ids=tuple(
                dict.fromkeys((*idea.consumer_ids, consumer_route_id))
            ),
            claim_intents=updated_intents,
            branch_provenance=branches,
        )
        self.proof_ideas[idea_id] = updated_idea
        route_metadata["proof_idea_id"] = idea_id
        route_metadata["claim_id"] = matched_intent.claim_id
        route_metadata["statement_identity"] = (
            requested_statement_identity or matched_intent.statement_identity
        )
        if consumer_branch_id:
            route_metadata["branch_id"] = consumer_branch_id
        route.metadata = route_metadata
        return matched_intent.claim_id

    def reconcile_proof_idea_graph_consumers(self) -> int:
        """Repair derived route consumers from exact graph lineage evidence.

        Mini-recursive routes and later semantic coalescing can make a route
        consume an executable node after the planner's original proof-idea
        record was created.  Older checkpoints therefore contain graph edges
        whose route/node lineage identifies a unique idea formulation, while
        the conserved idea still lists only the original root route.  Frontier
        packets generated from that split state are necessarily stale.

        Reconcile only exact structural identities, and only across explicit
        route-dependency edges (or a derived route's own stamped identity).
        Ambiguous identities remain untouched and fail closed.  The operation
        is idempotent and intentionally runs before scheduler packet sealing.
        """

        graph = self.proof_graph
        if graph is None or not self.proof_ideas:
            return 0
        registrations: Set[Tuple[str, str, str, str, str]] = set()

        def add_candidate(
            *,
            route: Any,
            node: Any = None,
        ) -> None:
            if (
                route is None
                or str(getattr(route, "kind", "") or "") != "strategy_route"
            ):
                return
            route_metadata = dict(getattr(route, "metadata", {}) or {})
            node_metadata = (
                dict(getattr(node, "metadata", {}) or {})
                if node is not None
                else {}
            )
            try:
                route_lineage = ProofLineageEnvelope.from_metadata(route_metadata)
            except (TypeError, ValueError):
                route_lineage = ProofLineageEnvelope()
            try:
                node_lineage = ProofLineageEnvelope.from_metadata(node_metadata)
            except (TypeError, ValueError):
                node_lineage = ProofLineageEnvelope()
            idea_id = str(
                route_lineage.proof_idea_id
                or node_lineage.proof_idea_id
                or route_metadata.get("proof_idea_id")
                or node_metadata.get("proof_idea_id")
                or ""
            ).strip()
            if idea_id not in self.proof_ideas:
                return
            statement_identity = str(
                node_lineage.statement_identity
                or (
                    graph_node_bound_contract_identity(node)
                    if node is not None
                    else ""
                )
                or route_lineage.statement_identity
                or route_metadata.get("structural_statement_identity")
                or ""
            ).strip()
            if not statement_identity:
                return
            claim_id = str(
                node_lineage.claim_id
                or route_lineage.claim_id
                or route_metadata.get("claim_id")
                or ""
            ).strip()
            branch_id = str(
                route_metadata.get("branch_id")
                or node_metadata.get("branch_id")
                or ""
            ).strip()
            registrations.add(
                (
                    idea_id,
                    str(route.node_id or "").strip(),
                    claim_id,
                    statement_identity,
                    branch_id,
                )
            )

        # Derived routes may already carry the exact lifecycle identity even
        # when their dependency node was omitted by an older checkpoint.
        for route in graph.nodes_by_kind("strategy_route"):
            metadata = dict(getattr(route, "metadata", {}) or {})
            if (
                str(metadata.get("route_scope") or "").strip() == "partial_route"
                or str(metadata.get("parent_route_id") or "").strip()
            ):
                add_candidate(route=route)

        # Shared/coalesced executable nodes own the exact claim identity; every
        # dependency route is a real consumer occurrence, including routes
        # that predate proof-idea tracking and consequently lack route stamps.
        for node in list(graph.nodes.values()):
            node_metadata = dict(getattr(node, "metadata", {}) or {})
            try:
                node_lineage = ProofLineageEnvelope.from_metadata(node_metadata)
            except (TypeError, ValueError):
                continue
            if not node_lineage.proof_idea_id:
                continue
            for edge in graph.incoming(node.node_id):
                if edge.kind not in _ROUTE_DEPENDENCY_EDGE_KINDS:
                    continue
                route = graph.nodes.get(edge.source)
                add_candidate(route=route, node=node)

        repaired = 0
        for idea_id, route_id, claim_id, statement_identity, branch_id in sorted(
            registrations
        ):
            idea = self.proof_ideas.get(idea_id)
            before = bool(
                isinstance(idea, ProofIdeaRecord)
                and route_id in idea.consumer_ids
                and any(
                    route_id in intent.consumer_ids
                    and statement_identity
                    in {
                        intent.statement_identity,
                        *intent.alternative_statement_identities,
                    }
                    for intent in idea.claim_intents
                )
            )
            registered_claim_id = self.register_proof_idea_consumer(
                proof_idea_id=idea_id,
                route_id=route_id,
                claim_id=claim_id,
                statement_identity=statement_identity,
                branch_id=branch_id,
                branch_source="graph_consumer_reconciliation",
            )
            if registered_claim_id and not before:
                repaired += 1
        if repaired:
            self.increment_tool_metric(
                "mini_proof_idea_graph_consumers_reconciled",
                repaired,
            )
        return repaired

    def merge_proof_ideas_from(self, other: "ProofDossier") -> int:
        """Import advisory lifecycle memory without changing proof authority."""

        changed = 0
        for record in dict(getattr(other, "proof_ideas", {}) or {}).values():
            if not isinstance(record, ProofIdeaRecord):
                continue
            before = self.proof_ideas.get(record.proof_idea_id)
            after = self.upsert_proof_idea(record)
            changed += int(before != after)
        return changed

    @staticmethod
    def _proof_idea_context_json_value(value: Any) -> Any:
        """Return a deterministic JSON projection without mutating graph state."""

        if value is None or isinstance(value, (str, int, float, bool)):
            return value
        if isinstance(value, Mapping):
            return {
                str(key): ProofDossier._proof_idea_context_json_value(item)
                for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
            }
        if isinstance(value, (list, tuple)):
            return [
                ProofDossier._proof_idea_context_json_value(item) for item in value
            ]
        if isinstance(value, (set, frozenset)):
            normalized = [
                ProofDossier._proof_idea_context_json_value(item) for item in value
            ]
            return sorted(
                normalized,
                key=lambda item: json.dumps(
                    item,
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=False,
                ),
            )
        if hasattr(value, "to_record") and callable(value.to_record):
            return ProofDossier._proof_idea_context_json_value(value.to_record())
        if hasattr(value, "__dataclass_fields__"):
            return ProofDossier._proof_idea_context_json_value(asdict(value))
        return {
            "unsupported_type": type(value).__name__,
            "stable_text": str(value),
        }

    def proof_idea_graph_revision(
        self,
        selected_work: Mapping[str, Any] | None = None,
    ) -> str:
        """Fingerprint the current graph view used for cognition resolution.

        This deliberately does not call ``ProofGraph.to_record`` because that
        serialization path performs graph maintenance. Context lookup is a
        read boundary and must remain pure.  When selected work is supplied,
        the revision is scoped to that cognition owner and its graph targets;
        unrelated scratch nodes and global attempt telemetry must not stale an
        otherwise unchanged prompt packet.
        """

        graph = self.proof_graph
        if graph is None:
            return ""
        if selected_work is None:
            payload = {
                "root_node_id": str(graph.root_node_id or ""),
                "nodes": [
                    {
                        "node_id": str(node_id),
                        "name": str(getattr(node, "name", "") or ""),
                        "kind": str(getattr(node, "kind", "") or ""),
                        "statement": str(getattr(node, "statement", "") or ""),
                        "status": str(getattr(node, "status", "") or ""),
                        "phase": str(getattr(node, "phase", "") or ""),
                        "turn_index": int(getattr(node, "turn_index", 0) or 0),
                        "metadata": self._proof_idea_context_json_value(
                            getattr(node, "metadata", {}) or {}
                        ),
                    }
                    for node_id, node in sorted(graph.nodes.items())
                ],
                "edges": sorted(
                    (
                        str(getattr(edge, "source", "") or ""),
                        str(getattr(edge, "target", "") or ""),
                        str(getattr(edge, "kind", "") or ""),
                    )
                    for edge in graph.edges
                ),
                "attempts": [
                    self._proof_idea_context_json_value(attempt)
                    for attempt in graph.attempts
                ],
                "active_root_target_statements": list(
                    graph.active_root_target_statements
                ),
                "active_root_target_contract_identities": list(
                    graph.active_root_target_contract_identities
                ),
            }
        else:
            layers = self._proof_idea_selected_work_layers(selected_work)
            relevant_node_ids: set[str] = set()
            proof_idea_ids: set[str] = set()
            proof_idea_bindings: Dict[
                str,
                List[ProofIdeaConsumerBinding],
            ] = {}

            def collect_binding(
                raw: Any,
                *,
                include_cognition_binding: bool = True,
            ) -> None:
                if isinstance(raw, ProofIdeaConsumerBinding):
                    binding = raw.to_record()
                elif isinstance(raw, Mapping):
                    binding = dict(raw)
                else:
                    return
                lineage = binding.get("proof_lineage")
                lineage_record = dict(lineage) if isinstance(lineage, Mapping) else {}
                idea_id = str(
                    binding.get("proof_idea_id")
                    or lineage_record.get("proof_idea_id")
                    or ""
                ).strip()
                if idea_id:
                    proof_idea_ids.add(idea_id)
                    try:
                        typed_binding = self._proof_idea_binding_from_packet(
                            binding
                        )
                    except (TypeError, ValueError):
                        typed_binding = (
                            self._proof_idea_binding_from_legacy(binding)
                            if include_cognition_binding
                            else None
                        )
                    if typed_binding is not None and include_cognition_binding:
                        bucket = proof_idea_bindings.setdefault(idea_id, [])
                        if typed_binding not in bucket:
                            bucket.append(typed_binding)
                for key in ("route_id", "claim_id", "graph_node_id"):
                    value = str(
                        binding.get(key) or lineage_record.get(key) or ""
                    ).strip()
                    if value:
                        relevant_node_ids.add(value)
                for value in list(binding.get("graph_node_ids") or []):
                    clean = str(value or "").strip()
                    if clean:
                        relevant_node_ids.add(clean)

            primary_binding_packets = [
                layer.get(key)
                for layer in layers
                for key in (
                    "primary_cognition_scope",
                    "primary_consumer_binding",
                )
                if layer.get(key) is not None
            ]
            for primary_packet in primary_binding_packets:
                collect_binding(primary_packet)

            for layer in layers:
                if layer.get("proof_idea_id") or layer.get("proof_lineage"):
                    collect_binding(
                        layer,
                        include_cognition_binding=not bool(
                            primary_binding_packets
                        ),
                    )
                raw_bindings = layer.get("consumer_bindings")
                if not primary_binding_packets and isinstance(
                    raw_bindings,
                    (list, tuple),
                ):
                    for raw_binding in raw_bindings:
                        collect_binding(raw_binding)
                lineage = layer.get("proof_lineage")
                if isinstance(lineage, Mapping):
                    collect_binding(
                        {"proof_lineage": lineage},
                        include_cognition_binding=not bool(
                            primary_binding_packets
                        ),
                    )
                work_type = str(layer.get("work_type") or "").strip()
                primary_fields = {
                    "formalize_claim": ("claim_id",),
                    "formalize_missing_obligation": ("obligation_id",),
                    "mine_missing_obligation": ("obligation_id",),
                    "prove_claim_variant": ("variant_id",),
                    "target_integrity_adjudication": ("obligation_id",),
                    "route_replan": ("replan_id",),
                    "assemble_route": ("route_id",),
                }.get(work_type, ("execution_target_graph_node_id",))
                for key in (*primary_fields, "execution_target_graph_node_id"):
                    value = str(layer.get(key) or "").strip()
                    if value:
                        relevant_node_ids.add(value)

                for key in (
                    "formalization_bridge_parent_obligation_id",
                    "claim_node_id",
                    "parent_claim_id",
                ):
                    value = str(layer.get(key) or "").strip()
                    if value:
                        relevant_node_ids.add(value)

            # Expand the execution owner to graph debt whose mutation changes
            # the selected action: route requirements and an obligation's
            # explicitly linked formalization parent.  Do not traverse generic
            # provenance edges, which would reintroduce sibling/scratch churn.
            expand_route_contract = any(
                str(layer.get("work_type") or "").strip()
                == "assemble_route"
                for layer in layers
            )
            pending_node_ids = list(relevant_node_ids)
            visited_node_ids: set[str] = set()
            while pending_node_ids:
                scoped_node_id = pending_node_ids.pop()
                if scoped_node_id in visited_node_ids:
                    continue
                visited_node_ids.add(scoped_node_id)
                scoped_node = graph.nodes.get(scoped_node_id)
                if scoped_node is None:
                    continue
                scoped_metadata = dict(
                    getattr(scoped_node, "metadata", {}) or {}
                )
                linked_ids: set[str] = set()
                for key in (
                    "formalization_bridge_parent_obligation_id",
                    "claim_node_id",
                    "parent_claim_id",
                ):
                    value = str(scoped_metadata.get(key) or "").strip()
                    if value:
                        linked_ids.add(value)
                for edge in graph.edges:
                    if (
                        str(getattr(edge, "source", "") or "")
                        == scoped_node_id
                        and str(getattr(edge, "kind", "") or "")
                        in {
                            "failure_requires",
                            "blocked_by",
                            "claim_formalized_as",
                        }
                    ):
                        linked_id = str(
                            getattr(edge, "target", "") or ""
                        ).strip()
                        if linked_id:
                            linked_ids.add(linked_id)
                if (
                    expand_route_contract
                    and str(getattr(scoped_node, "kind", "") or "")
                    == "strategy_route"
                ):
                    contract = scoped_metadata.get("route_assembly_contract")
                    if isinstance(contract, Mapping):
                        linked_ids.update(
                            str(value or "").strip()
                            for value in list(
                                contract.get("required_node_ids") or []
                            )
                            if str(value or "").strip()
                        )
                    dependency_edges = getattr(
                        graph,
                        "_route_dependency_edges",
                        None,
                    )
                    if callable(dependency_edges):
                        try:
                            linked_ids.update(
                                str(getattr(edge, "target", "") or "").strip()
                                for edge in dependency_edges(scoped_node_id)
                                if str(
                                    getattr(edge, "target", "") or ""
                                ).strip()
                            )
                        except Exception:
                            pass
                for linked_id in linked_ids:
                    if linked_id not in relevant_node_ids:
                        relevant_node_ids.add(linked_id)
                        pending_node_ids.append(linked_id)

            scoped_nodes = []
            for node_id in sorted(relevant_node_ids):
                node = graph.nodes.get(node_id)
                if node is None:
                    continue
                scoped_nodes.append(
                    {
                        "node_id": node_id,
                        "name": str(getattr(node, "name", "") or ""),
                        "kind": str(getattr(node, "kind", "") or ""),
                        "statement": str(getattr(node, "statement", "") or ""),
                        "status": str(getattr(node, "status", "") or ""),
                        "phase": str(getattr(node, "phase", "") or ""),
                        "turn_index": int(getattr(node, "turn_index", 0) or 0),
                        "metadata": self._proof_idea_context_json_value(
                            getattr(node, "metadata", {}) or {}
                        ),
                    }
                )
            payload = {
                "root_node_id": str(graph.root_node_id or ""),
                "scope_node_ids": sorted(relevant_node_ids),
                "nodes": scoped_nodes,
                "edges": sorted(
                    (
                        str(getattr(edge, "source", "") or ""),
                        str(getattr(edge, "target", "") or ""),
                        str(getattr(edge, "kind", "") or ""),
                    )
                    for edge in graph.edges
                    if str(getattr(edge, "source", "") or "")
                    in relevant_node_ids
                    and str(getattr(edge, "target", "") or "")
                    in relevant_node_ids
                ),
                "proof_ideas": {
                    idea_id: [
                        self._proof_idea_scoped_revision_record(
                            self.proof_ideas[idea_id],
                            binding,
                        )
                        for binding in proof_idea_bindings.get(idea_id, [])
                    ]
                    for idea_id in sorted(proof_idea_ids)
                    if idea_id in self.proof_ideas
                },
            }
            if expand_route_contract:
                # Route assembly prompts render the active framed root target.
                # Retargeting that frame must invalidate an already selected
                # assembly packet even when its route/node topology is stable.
                payload["active_root_target_statements"] = sorted(
                    str(value or "").strip()
                    for value in graph.active_root_target_statements
                    if str(value or "").strip()
                )
                payload["active_root_target_contract_identities"] = sorted(
                    str(value or "").strip()
                    for value in graph.active_root_target_contract_identities
                    if str(value or "").strip()
                )
        digest = hashlib.sha256(
            json.dumps(
                payload,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            ).encode("utf-8")
        ).hexdigest()
        return f"proof-graph-context:{digest}"

    @staticmethod
    def _proof_idea_selected_work_layers(
        selected_work: Mapping[str, Any] | None,
    ) -> List[Mapping[str, Any]]:
        return selected_work_mapping_layers(selected_work)

    @staticmethod
    def _proof_idea_binding_from_legacy(
        raw: Mapping[str, Any],
    ) -> Optional[ProofIdeaConsumerBinding]:
        try:
            envelope = ProofLineageEnvelope.from_metadata(raw)
        except (TypeError, ValueError):
            envelope = ProofLineageEnvelope()
        graph_node_ids = tuple(
            dict.fromkeys(
                str(raw.get(key) or "").strip()
                for key in ("graph_node_id", "node_id")
                if str(raw.get(key) or "").strip()
            )
        )
        if not any(
            (
                envelope.proof_idea_id,
                envelope.route_id,
                envelope.claim_id,
                envelope.statement_identity,
                graph_node_ids,
            )
        ):
            return None
        return ProofIdeaConsumerBinding.from_lineage(
            envelope,
            branch_id=str(raw.get("branch_id") or "").strip(),
            occurrence_key=str(
                raw.get("occurrence_key")
                or raw.get("selected_work_item_id")
                or raw.get("work_item_id")
                or ""
            ).strip(),
            graph_node_ids=graph_node_ids,
        )

    @staticmethod
    def _proof_idea_binding_from_packet(
        raw: Mapping[str, Any],
    ) -> ProofIdeaConsumerBinding:
        """Decode either the strict contract or the graph packet wrapper.

        The wrapper adapter is intentionally separate from
        ``ProofIdeaConsumerBinding.from_record``. Checkpoint/persistence input
        remains strict; only the known graph projection envelope is accepted
        here and unknown wrapper keys still fail closed.
        """

        typed_keys = set(ProofIdeaConsumerBinding.__dataclass_fields__)
        raw_keys = set(raw)
        if raw_keys.issubset(typed_keys):
            return ProofIdeaConsumerBinding.from_record(raw)
        wrapper_keys = {
            "consumer_binding_id",
            "proof_lineage",
            "branch_id",
            "reason",
            "graph_node_id",
            "graph_node_ids",
        }
        unknown = sorted(raw_keys - wrapper_keys)
        if unknown:
            raise ValueError(
                "unknown proof idea graph consumer wrapper fields: "
                + ", ".join(unknown)
            )
        proof_lineage = raw.get("proof_lineage")
        if not isinstance(proof_lineage, Mapping):
            raise ValueError(
                "proof idea graph consumer wrapper requires proof_lineage"
            )
        envelope = ProofLineageEnvelope.from_record(proof_lineage)
        graph_node_ids: List[str] = []
        raw_node_ids = raw.get("graph_node_ids")
        if isinstance(raw_node_ids, (list, tuple)):
            graph_node_ids.extend(
                str(item or "").strip()
                for item in raw_node_ids
                if str(item or "").strip()
            )
        graph_node_id = str(raw.get("graph_node_id") or "").strip()
        if graph_node_id:
            graph_node_ids.append(graph_node_id)
        return ProofIdeaConsumerBinding.from_lineage(
            envelope,
            branch_id=str(raw.get("branch_id") or "").strip(),
            occurrence_key=str(raw.get("consumer_binding_id") or "").strip(),
            graph_node_ids=tuple(graph_node_ids),
        )

    def _proof_idea_execution_scope(
        self,
        layers: Sequence[Mapping[str, Any]],
    ) -> ProofIdeaExecutionScope:
        partial_scope: Optional[ProofIdeaExecutionScope] = None
        for layer in layers:
            raw = layer.get("execution_scope")
            if isinstance(raw, ProofIdeaExecutionScope):
                parsed = raw
            if isinstance(raw, Mapping):
                parsed = ProofIdeaExecutionScope.from_record(raw)
            elif not isinstance(raw, ProofIdeaExecutionScope):
                continue
            if parsed.proposition_identity:
                return parsed
            if partial_scope is None:
                partial_scope = parsed
        if partial_scope is not None:
            for layer in layers:
                raw = layer.get("execution_scope")
                nested_proposition = (
                    str(raw.get("proposition_identity") or "").strip()
                    if isinstance(raw, Mapping)
                    else ""
                )
                proposition_identity = nested_proposition or str(
                    layer.get("execution_proposition_identity") or ""
                ).strip()
                if proposition_identity:
                    return replace(
                        partial_scope,
                        proposition_identity=proposition_identity,
                    )
            return partial_scope

        def first_value(*keys: str) -> Any:
            for layer in layers:
                for key in keys:
                    if key in layer and layer[key] not in (None, ""):
                        return layer[key]
            return ""

        target = first_value(
            "exact_target_statement",
            "target_statement",
            "selected_target_statement",
        )
        if not isinstance(target, str):
            raise TypeError("selected-work target_statement must be a string")
        return ProofIdeaExecutionScope(
            target_statement=target,
            statement_identity=str(
                first_value(
                    "execution_contract_identity",
                    "statement_identity",
                )
                or ""
            ),
            proposition_identity=str(
                first_value("execution_proposition_identity") or ""
            ),
            environment_hash=str(
                first_value(
                    "execution_environment_hash",
                    "environment_hash",
                    "statement_environment_hash",
                    "lean_environment_hash",
                )
                or ""
            ),
            helper_context_hash=str(
                first_value(
                    "execution_helper_context_hash",
                    "helper_context_hash",
                )
                or ""
            ),
            graph_revision=str(
                first_value("graph_revision", "proof_idea_graph_revision") or ""
            ),
        )

    def _proof_idea_binding_matches(
        self,
        binding: ProofIdeaConsumerBinding,
        idea: ProofIdeaRecord,
    ) -> bool:
        if binding.proof_idea_id and binding.proof_idea_id != idea.proof_idea_id:
            return False
        if binding.route_id and binding.route_id not in idea.consumer_ids and not any(
            binding.route_id in intent.consumer_ids for intent in idea.claim_intents
        ):
            return False
        if binding.claim_id and not any(
            intent.claim_id == binding.claim_id for intent in idea.claim_intents
        ):
            return False
        if binding.statement_identity and not any(
            binding.statement_identity
            in {
                intent.statement_identity,
                *intent.alternative_statement_identities,
            }
            for intent in idea.claim_intents
        ):
            return False
        branch_ids = {
            item.branch_id
            for item in idea.branch_provenance
            if str(item.branch_id or "").strip()
        }
        if len(branch_ids) > 1 and not binding.branch_id:
            return False
        if binding.branch_id and binding.branch_id not in {
            item.branch_id for item in idea.branch_provenance
        }:
            return False
        return True

    def _proof_idea_candidates_for_binding(
        self,
        binding: ProofIdeaConsumerBinding,
    ) -> List[Tuple[ProofIdeaConsumerBinding, ProofIdeaRecord]]:
        if binding.proof_idea_id:
            idea = self.proof_ideas.get(binding.proof_idea_id)
            return (
                [(binding, idea)]
                if isinstance(idea, ProofIdeaRecord)
                and self._proof_idea_binding_matches(binding, idea)
                else []
            )
        matches: List[Tuple[ProofIdeaConsumerBinding, ProofIdeaRecord]] = []
        for idea_id, idea in sorted(self.proof_ideas.items()):
            if not isinstance(idea, ProofIdeaRecord):
                continue
            resolved = replace(binding, proof_idea_id=idea_id)
            if self._proof_idea_binding_matches(resolved, idea):
                matches.append((resolved, idea))
        return matches

    def _proof_idea_scoped_observations(
        self,
        idea: ProofIdeaRecord,
        binding: ProofIdeaConsumerBinding,
    ) -> tuple[ProofIdeaObservation, ...]:
        matches: List[ProofIdeaObservation] = []
        for observation in idea.observations:
            if binding.branch_id and observation.branch_id != binding.branch_id:
                continue
            if binding.route_id:
                if observation.route_id and observation.route_id != binding.route_id:
                    continue
                if not observation.route_id and (
                    not binding.claim_id or observation.claim_id != binding.claim_id
                ):
                    continue
            if binding.claim_id:
                if observation.claim_id and observation.claim_id != binding.claim_id:
                    continue
                if not observation.claim_id and (
                    not binding.route_id or observation.route_id != binding.route_id
                ):
                    continue
            if (
                binding.proof_candidate_id
                and observation.proof_candidate_id
                and observation.proof_candidate_id != binding.proof_candidate_id
            ):
                continue
            if binding.lean_residual_id and observation.kind == "lean_residual":
                if observation.lean_residual_id != binding.lean_residual_id:
                    continue
            matches.append(observation)

        # Preserve one exact current unit for every evidence kind. Attempted
        # code and Lean output stay on the same immutable observation, so a
        # renderer can never pair a new residual with an older proof attempt.
        latest_by_kind: Dict[str, ProofIdeaObservation] = {}
        for observation in matches:
            existing = latest_by_kind.get(observation.kind)
            if existing is None or (
                observation.turn_index,
                observation.observation_id,
            ) > (existing.turn_index, existing.observation_id):
                latest_by_kind[observation.kind] = observation
        return tuple(
            sorted(
                latest_by_kind.values(),
                key=lambda item: (
                    item.turn_index,
                    item.kind,
                    item.observation_id,
                ),
            )
        )

    def _proof_idea_scoped_revision_record(
        self,
        idea: ProofIdeaRecord,
        binding: ProofIdeaConsumerBinding,
    ) -> Dict[str, Any]:
        """Project one idea onto the evidence rendered for one consumer."""

        matching_intents = [
            intent
            for intent in idea.claim_intents
            if (
                (binding.claim_id and intent.claim_id == binding.claim_id)
                or (
                    not binding.claim_id
                    and binding.statement_identity
                    and binding.statement_identity
                    in {
                        intent.statement_identity,
                        *intent.alternative_statement_identities,
                    }
                )
            )
        ]
        intent = matching_intents[0] if len(matching_intents) == 1 else None
        resolution = (
            idea.current_claim_resolution(intent.claim_id)
            if intent is not None
            else None
        )
        branch_provenance = [
            item.to_record()
            for item in idea.branch_provenance
            if not binding.branch_id or item.branch_id == binding.branch_id
        ]
        return {
            "proof_idea_id": idea.proof_idea_id,
            "parent_proof_idea_id": idea.parent_proof_idea_id,
            "strategy": idea.strategy,
            "notes": list(idea.notes),
            "current_status": idea.current_status,
            "current_status_authority": idea.current_status_authority,
            "binding": binding.to_record(),
            "branch_provenance": branch_provenance,
            "claim_intent": intent.to_record() if intent is not None else None,
            "claim_resolution": (
                resolution.to_record() if resolution is not None else None
            ),
            "observations": [
                item.to_record()
                for item in self._proof_idea_scoped_observations(idea, binding)
            ],
        }

    def _proof_idea_context_digest(
        self,
        resolution: ProofIdeaContextResolution,
    ) -> str:
        payload = {
            "status": resolution.status,
            "policy": resolution.policy,
            "reason": resolution.reason,
            "execution_scope": resolution.execution_scope.to_record(),
            "current_graph_revision": resolution.current_graph_revision,
            "primary_binding": (
                resolution.primary_binding.to_record()
                if resolution.primary_binding is not None
                else None
            ),
            "candidate_bindings": [
                item.to_record() for item in resolution.candidate_bindings
            ],
            "candidate_proof_idea_ids": list(
                resolution.candidate_proof_idea_ids
            ),
            "proof_idea": (
                self._proof_idea_scoped_revision_record(
                    resolution.proof_idea,
                    resolution.primary_binding,
                )
                if resolution.proof_idea is not None
                and resolution.primary_binding is not None
                else None
            ),
            "claim_intent": (
                resolution.claim_intent.to_record()
                if resolution.claim_intent is not None
                else None
            ),
            "claim_resolution": (
                resolution.claim_resolution.to_record()
                if resolution.claim_resolution is not None
                else None
            ),
            "observations": [
                item.to_record() for item in resolution.observations
            ],
        }
        return "proof-idea-context:" + hashlib.sha256(
            json.dumps(
                payload,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            ).encode("utf-8")
        ).hexdigest()

    def resolve_proof_idea_context(
        self,
        selected_work: Mapping[str, Any] | None,
        *,
        policy: str = "exact_selected",
    ) -> ProofIdeaContextResolution:
        """Resolve selected execution work to exactly one cognition owner.

        ``exact_selected`` never uses dossier cardinality or global route rank
        as a fallback. Ambiguous, missing, stale-environment, and stale-graph
        bindings remain explicit non-resolved results.
        """

        clean_policy = str(policy or "").strip()
        layers = self._proof_idea_selected_work_layers(selected_work)
        execution_scope = self._proof_idea_execution_scope(layers)
        current_revision = self.proof_idea_graph_revision(selected_work)

        def finish(
            *,
            resolved_revision_scope: Optional[Mapping[str, Any]] = None,
            **values: Any,
        ) -> ProofIdeaContextResolution:
            revision_scope_json = ""
            resolved_revision = current_revision
            if resolved_revision_scope is not None:
                normalized_scope = self._proof_idea_context_json_value(
                    resolved_revision_scope
                )
                if not isinstance(normalized_scope, Mapping):
                    raise TypeError(
                        "resolved proof-idea revision scope must be a mapping"
                    )
                revision_scope_json = json.dumps(
                    normalized_scope,
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=False,
                )
                resolved_revision = self.proof_idea_graph_revision(
                    normalized_scope
                )
            draft = ProofIdeaContextResolution(
                policy=clean_policy,
                execution_scope=execution_scope,
                current_graph_revision=resolved_revision,
                context_digest="",
                revision_scope_json=revision_scope_json,
                **values,
            )
            return replace(
                draft,
                context_digest=self._proof_idea_context_digest(draft),
            )

        if clean_policy == "protocol_only":
            return finish(
                status="unbound",
                reason="proof-idea context intentionally excluded by protocol policy",
            )

        explicit_primary: Optional[ProofIdeaConsumerBinding] = None
        explicit_primary_binding_id = ""
        bindings: List[ProofIdeaConsumerBinding] = []
        for layer in layers:
            raw_primary_binding_id = layer.get("primary_consumer_binding_id")
            if raw_primary_binding_id not in (None, ""):
                if not isinstance(raw_primary_binding_id, str):
                    raise TypeError(
                        "primary_consumer_binding_id must be a string"
                    )
                clean_primary_binding_id = raw_primary_binding_id.strip()
                if (
                    explicit_primary_binding_id
                    and explicit_primary_binding_id != clean_primary_binding_id
                ):
                    return finish(
                        status="ambiguous",
                        reason="selected work contains conflicting primary binding IDs",
                    )
                explicit_primary_binding_id = clean_primary_binding_id
            for key in ("primary_cognition_scope", "primary_consumer_binding"):
                raw_primary = layer.get(key)
                if isinstance(raw_primary, ProofIdeaConsumerBinding):
                    candidate = raw_primary
                elif isinstance(raw_primary, Mapping):
                    candidate = self._proof_idea_binding_from_packet(raw_primary)
                else:
                    continue
                if explicit_primary is not None and explicit_primary != candidate:
                    return finish(
                        status="ambiguous",
                        reason="selected work contains conflicting primary cognition scopes",
                        candidate_bindings=(explicit_primary, candidate),
                        candidate_proof_idea_ids=tuple(
                            value
                            for value in (
                                explicit_primary.proof_idea_id,
                                candidate.proof_idea_id,
                            )
                            if value
                        ),
                    )
                explicit_primary = candidate
            raw_bindings = layer.get("consumer_bindings")
            if isinstance(raw_bindings, (list, tuple)):
                for raw_binding in raw_bindings:
                    if isinstance(raw_binding, ProofIdeaConsumerBinding):
                        bindings.append(raw_binding)
                    elif isinstance(raw_binding, Mapping):
                        bindings.append(
                            self._proof_idea_binding_from_packet(raw_binding)
                        )
            legacy = self._proof_idea_binding_from_legacy(layer)
            if legacy is not None:
                bindings.append(legacy)

        graph = self.proof_graph
        if graph is not None:
            graph_node_ids = {
                node_id
                for layer in layers
                for key in (
                    "graph_node_id",
                    "node_id",
                    "route_id",
                    "claim_id",
                    "variant_id",
                    "obligation_id",
                    "replan_id",
                )
                for node_id in [str(layer.get(key) or "").strip()]
                if node_id
            }
            for node_id in sorted(graph_node_ids):
                node = graph.nodes.get(node_id)
                if node is None:
                    continue
                metadata = dict(getattr(node, "metadata", {}) or {})
                metadata.setdefault("graph_node_id", node_id)
                derived = self._proof_idea_binding_from_legacy(metadata)
                if derived is not None:
                    bindings.append(derived)

        if explicit_primary is not None:
            bindings.insert(0, explicit_primary)
        deduplicated: Dict[Tuple[Any, ...], ProofIdeaConsumerBinding] = {}
        for binding in bindings:
            key = (
                binding.proof_idea_id,
                binding.route_id,
                binding.claim_id,
                binding.statement_identity,
                binding.branch_id,
                binding.occurrence_key,
                binding.proof_candidate_id,
                binding.lean_residual_id,
                binding.repair_ticket_id,
                binding.graph_node_ids,
            )
            deduplicated[key] = binding
        bindings = list(deduplicated.values())

        if explicit_primary is None and explicit_primary_binding_id:
            primary_matches = [
                binding
                for binding in bindings
                if binding.occurrence_key == explicit_primary_binding_id
            ]
            if len(primary_matches) != 1:
                return finish(
                    status=("unbound" if not primary_matches else "ambiguous"),
                    reason=(
                        "primary consumer binding ID does not identify a binding"
                        if not primary_matches
                        else "primary consumer binding ID is not unique"
                    ),
                    candidate_bindings=tuple(bindings),
                    candidate_proof_idea_ids=tuple(
                        binding.proof_idea_id
                        for binding in primary_matches
                        if binding.proof_idea_id
                    ),
                )
            explicit_primary = primary_matches[0]

        expanded: List[Tuple[ProofIdeaConsumerBinding, ProofIdeaRecord]] = []
        search_bindings = [explicit_primary] if explicit_primary is not None else bindings
        for binding in search_bindings:
            if binding is not None:
                expanded.extend(self._proof_idea_candidates_for_binding(binding))
        expanded_by_idea: Dict[str, Tuple[ProofIdeaConsumerBinding, ProofIdeaRecord]] = {}
        expanded_by_cognition: Dict[
            Tuple[str, str, str, str, str],
            Tuple[ProofIdeaConsumerBinding, ProofIdeaRecord],
        ] = {}
        for binding, idea in expanded:
            expanded_by_idea.setdefault(idea.proof_idea_id, (binding, idea))
            expanded_by_cognition.setdefault(
                (
                    idea.proof_idea_id,
                    binding.route_id,
                    binding.claim_id,
                    binding.statement_identity,
                    binding.branch_id,
                ),
                (binding, idea),
            )

        candidate_ids = tuple(sorted(expanded_by_idea))
        if explicit_primary is not None and explicit_primary.proof_idea_id:
            if explicit_primary.proof_idea_id not in self.proof_ideas:
                return finish(
                    status="stale",
                    reason="selected proof idea no longer exists in the dossier",
                    primary_binding=explicit_primary,
                    candidate_bindings=tuple(bindings),
                    candidate_proof_idea_ids=(explicit_primary.proof_idea_id,),
                )
            if not expanded:
                return finish(
                    status="stale",
                    reason="selected cognition coordinates no longer match the proof idea",
                    primary_binding=explicit_primary,
                    candidate_bindings=tuple(bindings),
                    candidate_proof_idea_ids=(explicit_primary.proof_idea_id,),
                )
        if not candidate_ids:
            return finish(
                status="unbound",
                reason="selected work has no explicit proof-idea cognition binding",
                candidate_bindings=tuple(bindings),
            )
        if explicit_primary is None and len(expanded_by_cognition) != 1:
            return finish(
                status="ambiguous",
                reason="selected work has multiple cognition consumers and no primary",
                candidate_bindings=tuple(
                    binding for binding, _idea in expanded_by_cognition.values()
                ),
                candidate_proof_idea_ids=candidate_ids,
            )
        if len(candidate_ids) != 1:
            return finish(
                status="ambiguous",
                reason="selected work maps to multiple proof-idea cognition owners",
                candidate_bindings=tuple(binding for binding, _idea in expanded),
                candidate_proof_idea_ids=candidate_ids,
            )

        binding, idea = expanded_by_idea[candidate_ids[0]]
        if execution_scope.environment_hash and (
            execution_scope.environment_hash
            != str(self.current_lean_environment_hash or "").strip()
        ):
            return finish(
                status="stale",
                reason="selected execution environment differs from the current environment",
                primary_binding=binding,
                candidate_bindings=tuple(bindings),
                candidate_proof_idea_ids=candidate_ids,
            )
        if execution_scope.graph_revision and (
            execution_scope.graph_revision != current_revision
        ):
            # Accept a packet stamped by the pre-scoped revision scheme only
            # when it still equals the current whole-graph revision. Newly
            # stamped packets use the scoped revision above.
            if execution_scope.graph_revision != self.proof_idea_graph_revision():
                return finish(
                    status="stale",
                    reason="selected graph revision differs from the current graph revision",
                    primary_binding=binding,
                    candidate_bindings=tuple(bindings),
                    candidate_proof_idea_ids=candidate_ids,
                )
        if (
            execution_scope.statement_identity
            and binding.statement_identity
            and execution_scope.statement_identity != binding.statement_identity
        ):
            return finish(
                status="stale",
                reason="selected execution contract differs from cognition statement",
                primary_binding=binding,
                candidate_bindings=tuple(bindings),
                candidate_proof_idea_ids=candidate_ids,
            )
        declared_exact_targets = {
            str(layer.get(key) or "")
            for layer in layers
            for key in (
                "exact_target_statement",
                "target_statement",
                "selected_target_statement",
            )
            if layer.get(key) not in (None, "")
        }
        if execution_scope.target_statement:
            declared_exact_targets.add(execution_scope.target_statement)
        if len(declared_exact_targets) > 1:
            return finish(
                status="stale",
                reason="selected work contains conflicting exact target statements",
                primary_binding=binding,
                candidate_bindings=tuple(bindings),
                candidate_proof_idea_ids=candidate_ids,
            )
        execution_target_node_ids = {
            str(layer.get("execution_target_graph_node_id") or "").strip()
            for layer in layers
            if str(layer.get("execution_target_graph_node_id") or "").strip()
        }
        if len(execution_target_node_ids) > 1:
            return finish(
                status="stale",
                reason="selected work contains conflicting execution target nodes",
                primary_binding=binding,
                candidate_bindings=tuple(bindings),
                candidate_proof_idea_ids=candidate_ids,
            )
        execution_target_node_id = next(iter(execution_target_node_ids), "")
        work_types = {
            str(layer.get("work_type") or "").strip()
            for layer in layers
            if str(layer.get("work_type") or "").strip()
        }
        if graph is not None and execution_target_node_id:
            execution_target_node = graph.nodes.get(execution_target_node_id)
            if execution_target_node is None:
                return finish(
                    status="stale",
                    reason="selected execution target graph node no longer exists",
                    primary_binding=binding,
                    candidate_bindings=tuple(bindings),
                    candidate_proof_idea_ids=candidate_ids,
                )
            if "assemble_route" in work_types:
                if execution_target_node_id != graph.root_node_id:
                    return finish(
                        status="stale",
                        reason="selected route assembly no longer targets the graph root",
                        primary_binding=binding,
                        candidate_bindings=tuple(bindings),
                        candidate_proof_idea_ids=candidate_ids,
                    )
            elif (
                binding.graph_node_ids
                and execution_target_node_id not in binding.graph_node_ids
            ):
                return finish(
                    status="stale",
                    reason="selected execution target is outside its cognition binding",
                    primary_binding=binding,
                    candidate_bindings=tuple(bindings),
                    candidate_proof_idea_ids=candidate_ids,
                )
            if (
                execution_scope.target_statement
                != str(getattr(execution_target_node, "statement", "") or "")
            ):
                return finish(
                    status="stale",
                    reason="selected exact target differs from its execution graph node",
                    primary_binding=binding,
                    candidate_bindings=tuple(bindings),
                    candidate_proof_idea_ids=candidate_ids,
                )
        owning_route = None
        owning_route_branch_id = ""
        if graph is not None and binding.route_id:
            owning_route = graph.nodes.get(binding.route_id)
            if owning_route is None or owning_route.kind != "strategy_route":
                return finish(
                    status="stale",
                    reason="selected cognition route no longer exists",
                    primary_binding=binding,
                    candidate_bindings=tuple(bindings),
                    candidate_proof_idea_ids=candidate_ids,
                )
            owning_route_metadata = dict(owning_route.metadata or {})
            try:
                owning_route_lineage = ProofLineageEnvelope.from_metadata(
                    owning_route_metadata
                )
            except (TypeError, ValueError):
                owning_route_lineage = ProofLineageEnvelope()
            if (
                owning_route_lineage.proof_idea_id
                and owning_route_lineage.proof_idea_id != idea.proof_idea_id
            ):
                return finish(
                    status="stale",
                    reason="selected route belongs to a different proof idea",
                    primary_binding=binding,
                    candidate_bindings=tuple(bindings),
                    candidate_proof_idea_ids=candidate_ids,
                )
            owning_route_branch_id = str(
                owning_route_metadata.get("branch_id") or ""
            ).strip()
            if (
                binding.branch_id
                and owning_route_branch_id
                and binding.branch_id != owning_route_branch_id
            ):
                return finish(
                    status="stale",
                    reason="selected route belongs to a different branch",
                    primary_binding=binding,
                    candidate_bindings=tuple(bindings),
                    candidate_proof_idea_ids=candidate_ids,
                )
        if graph is not None and binding.graph_node_ids:
            missing = [
                node_id
                for node_id in binding.graph_node_ids
                if node_id not in graph.nodes
            ]
            if missing:
                return finish(
                    status="stale",
                    reason="selected cognition graph nodes no longer exist: "
                    + ", ".join(missing),
                    primary_binding=binding,
                    candidate_bindings=tuple(bindings),
                    candidate_proof_idea_ids=candidate_ids,
                )
            exact_target_nodes = [
                graph.nodes[node_id]
                for node_id in binding.graph_node_ids
                if graph.nodes[node_id].kind != "strategy_route"
            ]
            if (
                not execution_target_node_id
                and execution_scope.target_statement
                and exact_target_nodes
                and not any(
                    execution_scope.target_statement
                    == str(getattr(node, "statement", "") or "")
                    for node in exact_target_nodes
                )
            ):
                return finish(
                    status="stale",
                    reason="selected exact target differs from its cognition graph node",
                    primary_binding=binding,
                    candidate_bindings=tuple(bindings),
                    candidate_proof_idea_ids=candidate_ids,
                )
            for node_id in binding.graph_node_ids:
                node = graph.nodes[node_id]
                node_metadata = dict(getattr(node, "metadata", {}) or {})
                try:
                    node_lineage = ProofLineageEnvelope.from_metadata(node_metadata)
                except (TypeError, ValueError):
                    node_lineage = ProofLineageEnvelope()
                if (
                    owning_route is None
                    and node_lineage.proof_idea_id
                    and node_lineage.proof_idea_id != idea.proof_idea_id
                ):
                    return finish(
                        status="stale",
                        reason="selected graph node belongs to a different proof idea",
                        primary_binding=binding,
                        candidate_bindings=tuple(bindings),
                        candidate_proof_idea_ids=candidate_ids,
                    )
                node_branch_id = str(node_metadata.get("branch_id") or "").strip()
                if (
                    owning_route is None
                    and binding.branch_id
                    and node_branch_id
                    and binding.branch_id != node_branch_id
                ):
                    return finish(
                        status="stale",
                        reason="selected graph node belongs to a different branch",
                        primary_binding=binding,
                        candidate_bindings=tuple(bindings),
                        candidate_proof_idea_ids=candidate_ids,
                    )
                if str(getattr(node, "status", "") or "") in {
                    "invalidated",
                    "superseded",
                }:
                    return finish(
                        status="stale",
                        reason="selected graph node is terminally stale",
                        primary_binding=binding,
                        candidate_bindings=tuple(bindings),
                        candidate_proof_idea_ids=candidate_ids,
                    )
        elif graph is not None:
            missing_coordinates = [
                node_id
                for node_id in (binding.route_id,)
                if node_id and node_id not in graph.nodes
            ]
            if missing_coordinates:
                return finish(
                    status="stale",
                    reason="selected cognition graph coordinates no longer exist: "
                    + ", ".join(missing_coordinates),
                    primary_binding=binding,
                    candidate_bindings=tuple(bindings),
                    candidate_proof_idea_ids=candidate_ids,
                )

        matching_intents = [
            intent
            for intent in idea.claim_intents
            if (
                (binding.claim_id and intent.claim_id == binding.claim_id)
                or (
                    not binding.claim_id
                    and binding.statement_identity
                    and binding.statement_identity
                    in {
                        intent.statement_identity,
                        *intent.alternative_statement_identities,
                    }
                )
            )
        ]
        if len(matching_intents) > 1:
            return finish(
                status="ambiguous",
                reason="selected cognition maps to multiple claim intents",
                candidate_bindings=tuple(bindings),
                candidate_proof_idea_ids=candidate_ids,
            )
        claim_intent = matching_intents[0] if matching_intents else None
        claim_resolution = (
            idea.current_claim_resolution(claim_intent.claim_id)
            if claim_intent is not None
            else None
        )
        observations = self._proof_idea_scoped_observations(idea, binding)
        resolved_revision_scope = dict(selected_work or {})
        # Bind freshness to the proof idea actually selected by graph-derived
        # lineage as well as to the original execution packet.  Without this
        # enrichment resolution and projection compute different scopes; with
        # only the raw scope, proof-idea text could change undetected.
        resolved_revision_scope["primary_cognition_scope"] = binding.to_record()
        return finish(
            status="resolved",
            reason="selected cognition binding resolved exactly",
            resolved_revision_scope=resolved_revision_scope,
            primary_binding=binding,
            candidate_bindings=tuple(bindings),
            candidate_proof_idea_ids=candidate_ids,
            proof_idea=idea,
            claim_intent=claim_intent,
            claim_resolution=claim_resolution,
            observations=observations,
        )

    def _proof_idea_context_evidence(
        self,
        kind: str,
        content: str,
    ) -> ProofIdeaContextEvidence:
        """Authorize one full unit or withhold it with an integrity receipt."""

        value = strip_legacy_placeholder_corruption_for_prompt(
            str(content or "")
        )
        answer_safety = self._answer_safety_kwargs()
        if is_answer_unsafe_statement_text(value, **answer_safety) or (
            is_answer_unsafe_helper_source(value, **answer_safety)
        ):
            return ProofIdeaContextEvidence.withheld(
                kind,
                value,
                reason="answer visibility policy",
            )
        return ProofIdeaContextEvidence.exact(kind, value)

    def project_proof_idea_context(
        self,
        resolution: ProofIdeaContextResolution,
        *,
        audience: str,
    ) -> ProofIdeaContextProjection:
        """Create a pure, audience-specific packet of whole evidence units."""

        if not isinstance(resolution, ProofIdeaContextResolution):
            raise TypeError("proof idea context projection requires a resolution")
        if resolution.status == "resolved":
            if resolution.revision_scope_json:
                revision_packet = json.loads(resolution.revision_scope_json)
            else:
                # Compatibility for manually constructed resolution values.
                revision_packet = {
                    "execution_scope": resolution.execution_scope.to_record(),
                }
                if resolution.primary_binding is not None:
                    revision_packet["primary_cognition_scope"] = (
                        resolution.primary_binding.to_record()
                    )
            current_revision = self.proof_idea_graph_revision(revision_packet)
            if resolution.current_graph_revision != current_revision:
                raise StaleProofIdeaContextProjectionError(
                    "proof idea context resolution is stale; graph changed after resolution"
                )
            if resolution.execution_scope.environment_hash and (
                resolution.execution_scope.environment_hash
                != str(self.current_lean_environment_hash or "").strip()
            ):
                raise StaleProofIdeaContextProjectionError(
                    "proof idea context resolution is stale; environment changed after resolution"
                )
        target = self._proof_idea_context_evidence(
            "active_target",
            resolution.execution_scope.target_statement,
        )
        evidence: List[ProofIdeaContextEvidence] = []

        def add(kind: str, value: Any) -> None:
            text = str(value or "")
            if text:
                evidence.append(self._proof_idea_context_evidence(kind, text))

        add("resolution_reason", resolution.reason)
        binding = resolution.primary_binding
        idea = resolution.proof_idea
        if resolution.status == "resolved" and binding is not None and idea is not None:
            add(
                "cognition_scope",
                json.dumps(
                    binding.to_record(),
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=False,
                ),
            )
            add("strategy", idea.strategy)
            add("strategy_notes", "\n".join(idea.notes))
            add(
                "strategy_status",
                json.dumps(
                    {
                        "status": idea.current_status,
                        "authority": idea.current_status_authority,
                        "proof_authority": False,
                    },
                    sort_keys=True,
                    separators=(",", ":"),
                ),
            )
            intent = resolution.claim_intent
            if intent is not None:
                add("claim_statement", intent.statement)
                add("claim_purpose", intent.rationale)
                add(
                    "claim_rationale_alternatives",
                    "\n".join(intent.rationale_alternatives),
                )
                add(
                    "claim_formulation_alternatives",
                    "\n".join(intent.alternative_statements),
                )
                add(
                    "claim_dependencies",
                    json.dumps(
                        {
                            "claim_ids": list(intent.dependency_claim_ids),
                            "labels": list(intent.dependency_labels),
                            "invariants": list(intent.invariant_refs),
                        },
                        sort_keys=True,
                        separators=(",", ":"),
                        ensure_ascii=False,
                    ),
                )
            if resolution.claim_resolution is not None:
                add(
                    "claim_resolution",
                    json.dumps(
                        resolution.claim_resolution.to_record(),
                        sort_keys=True,
                        separators=(",", ":"),
                        ensure_ascii=False,
                    ),
                )

            for observation in resolution.observations:
                coordinates = {
                    "observation_id": observation.observation_id,
                    "kind": observation.kind,
                    "claim_id": observation.claim_id,
                    "route_id": observation.route_id,
                    "branch_id": observation.branch_id,
                    "attempt_id": observation.attempt_id,
                    "proof_candidate_id": observation.proof_candidate_id,
                    "lean_residual_id": observation.lean_residual_id,
                    "turn_index": observation.turn_index,
                }
                add(
                    f"observation_coordinates:{observation.kind}",
                    json.dumps(
                        coordinates,
                        sort_keys=True,
                        separators=(",", ":"),
                        ensure_ascii=False,
                    ),
                )
                add(f"observation_summary:{observation.kind}", observation.summary)
                add(
                    f"near_theorems:{observation.kind}",
                    "\n".join(observation.theorem_names),
                )
                if audience != "theory":
                    add(
                        f"attempted_lean:{observation.kind}",
                        observation.attempted_lean_code,
                    )
                    if observation.exact_lean_output:
                        add(
                            f"exact_lean_output:{observation.kind}",
                            observation.exact_lean_output,
                        )
                    elif observation.lean_output_preview:
                        if observation.result_sha256 and observation.result_length:
                            preview = ProofIdeaContextEvidence.preview(
                                f"lean_output_preview:{observation.kind}",
                                observation.lean_output_preview,
                                original_sha256=observation.result_sha256,
                                original_char_length=observation.result_length,
                            )
                            if is_answer_unsafe_statement_text(
                                preview.content,
                                **self._answer_safety_kwargs(),
                            ) or is_answer_unsafe_helper_source(
                                preview.content,
                                **self._answer_safety_kwargs(),
                            ):
                                preview = ProofIdeaContextEvidence.withheld_receipt(
                                    preview.kind,
                                    sha256=preview.sha256,
                                    char_length=preview.char_length,
                                    reason="answer visibility policy",
                                )
                            evidence.append(preview)
                        else:
                            add(
                                f"stored_lean_output_preview:{observation.kind}",
                                observation.lean_output_preview,
                            )
                            add(
                                f"stored_lean_output_original_length:{observation.kind}",
                                str(observation.result_length),
                            )
                add(
                    f"observation_source:{observation.kind}",
                    json.dumps(
                        {
                            "pass_index": observation.source_pass_index,
                            "trigger": observation.source_trigger,
                            "model_id": observation.source_model_id,
                            "helpers_seen": observation.source_helpers_seen,
                            "reasoning_tokens": observation.source_reasoning_tokens,
                        },
                        sort_keys=True,
                        separators=(",", ":"),
                        ensure_ascii=False,
                    ),
                )

        return ProofIdeaContextProjection(
            audience=audience,
            resolution_status=resolution.status,
            context_digest=resolution.context_digest,
            target=target,
            evidence=tuple(evidence),
            proof_authority=False,
        )

    def project_global_proof_idea_context(
        self,
        *,
        audience: str = "planner",
    ) -> ProofIdeaGlobalContextProjection:
        """Project every lifecycle without pretending one is selected work.

        This is deliberately separate from ``resolve_proof_idea_context``.
        Planner/root inventory must never become an implicit ownership fallback
        for an exact graph task.
        """

        records = [
            idea
            for _idea_id, idea in sorted(self.proof_ideas.items())
            if isinstance(idea, ProofIdeaRecord)
        ]
        digest_payload = {
            "audience": str(audience or ""),
            "environment_hash": str(self.current_lean_environment_hash or ""),
            "graph_revision": self.proof_idea_graph_revision(),
            "proof_ideas": [idea.to_record() for idea in records],
        }
        context_digest = "proof-idea-global-context:" + hashlib.sha256(
            json.dumps(
                digest_payload,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            ).encode("utf-8")
        ).hexdigest()
        evidence: List[ProofIdeaContextEvidence] = []

        def add(kind: str, value: Any) -> None:
            text = str(value or "")
            if text:
                evidence.append(self._proof_idea_context_evidence(kind, text))

        for idea in records:
            idea_key = idea.proof_idea_id
            add(
                f"idea_identity:{idea_key}",
                json.dumps(
                    {
                        "proof_idea_id": idea.proof_idea_id,
                        "parent_proof_idea_id": idea.parent_proof_idea_id,
                        "theorem_name": idea.theorem_name,
                        "root_statement_identity": idea.root_statement_identity,
                        "route_shape_identity": idea.route_shape_identity,
                        "consumer_ids": list(idea.consumer_ids),
                        "proof_authority": False,
                    },
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=False,
                ),
            )
            add(f"idea_strategy:{idea_key}", idea.strategy)
            add(f"idea_notes:{idea_key}", "\n".join(idea.notes))
            add(
                f"idea_status_history:{idea_key}",
                json.dumps(
                    [item.to_record() for item in idea.status_history],
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=False,
                ),
            )
            add(
                f"idea_branch_provenance:{idea_key}",
                json.dumps(
                    [item.to_record() for item in idea.branch_provenance],
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=False,
                ),
            )
            for intent in idea.claim_intents:
                add(
                    f"idea_claim_intent:{idea_key}:{intent.claim_id}",
                    json.dumps(
                        intent.to_record(),
                        sort_keys=True,
                        separators=(",", ":"),
                        ensure_ascii=False,
                    ),
                )
            for claim_resolution in idea.claim_resolutions:
                add(
                    "idea_claim_resolution:"
                    f"{idea_key}:{claim_resolution.resolution_id}",
                    json.dumps(
                        claim_resolution.to_record(),
                        sort_keys=True,
                        separators=(",", ":"),
                        ensure_ascii=False,
                    ),
                )
            for observation in sorted(
                idea.observations,
                key=lambda item: (
                    item.turn_index,
                    item.branch_id,
                    item.route_id,
                    item.claim_id,
                    item.kind,
                    item.observation_id,
                ),
            ):
                observation_key = f"{idea_key}:{observation.observation_id}"
                add(
                    f"idea_observation_coordinates:{observation_key}",
                    json.dumps(
                        {
                            "kind": observation.kind,
                            "claim_id": observation.claim_id,
                            "route_id": observation.route_id,
                            "branch_id": observation.branch_id,
                            "attempt_id": observation.attempt_id,
                            "proof_candidate_id": observation.proof_candidate_id,
                            "lean_residual_id": observation.lean_residual_id,
                            "turn_index": observation.turn_index,
                        },
                        sort_keys=True,
                        separators=(",", ":"),
                        ensure_ascii=False,
                    ),
                )
                add(
                    f"idea_observation_summary:{observation_key}",
                    observation.summary,
                )
                add(
                    f"idea_near_theorems:{observation_key}",
                    "\n".join(observation.theorem_names),
                )
                if audience != "theory":
                    add(
                        f"idea_attempted_lean:{observation_key}",
                        observation.attempted_lean_code,
                    )
                    add(
                        f"idea_exact_lean_output:{observation_key}",
                        observation.exact_lean_output,
                    )
                    if observation.lean_output_preview:
                        if observation.result_sha256 and observation.result_length:
                            preview_evidence = ProofIdeaContextEvidence.preview(
                                f"idea_lean_output_preview:{observation_key}",
                                observation.lean_output_preview,
                                original_sha256=observation.result_sha256,
                                original_char_length=observation.result_length,
                            )
                            answer_safety = self._answer_safety_kwargs()
                            if is_answer_unsafe_statement_text(
                                preview_evidence.content,
                                **answer_safety,
                            ) or is_answer_unsafe_helper_source(
                                preview_evidence.content,
                                **answer_safety,
                            ):
                                preview_evidence = (
                                    ProofIdeaContextEvidence.withheld_receipt(
                                        preview_evidence.kind,
                                        sha256=preview_evidence.sha256,
                                        char_length=preview_evidence.char_length,
                                        reason="answer visibility policy",
                                    )
                                )
                            evidence.append(preview_evidence)
                        else:
                            add(
                                f"idea_stored_lean_output_preview:{observation_key}",
                                observation.lean_output_preview,
                            )
                            add(
                                "idea_stored_lean_output_original_length:"
                                f"{observation_key}",
                                str(observation.result_length),
                            )
                add(
                    f"idea_observation_source:{observation_key}",
                    json.dumps(
                        {
                            "pass_index": observation.source_pass_index,
                            "trigger": observation.source_trigger,
                            "model_id": observation.source_model_id,
                            "helpers_seen": observation.source_helpers_seen,
                            "reasoning_tokens": observation.source_reasoning_tokens,
                            "visible_output": observation.source_visible_output,
                        },
                        sort_keys=True,
                        separators=(",", ":"),
                        ensure_ascii=False,
                    ),
                )

        return ProofIdeaGlobalContextProjection(
            audience=audience,
            context_digest=context_digest,
            evidence=tuple(evidence),
            proof_authority=False,
        )

    def record_proof_idea_observation(
        self,
        proof_idea_id: str,
        observation: ProofIdeaObservation,
        *,
        branch_source: str = "mini_prover",
    ) -> bool:
        """Attach one exact discovery/residual to its owning strategy."""

        idea_id = str(proof_idea_id or "").strip()
        existing = self.proof_ideas.get(idea_id)
        if existing is None or not isinstance(observation, ProofIdeaObservation):
            return False
        observation_content = observation.to_record()
        occurrence_key = str(observation_content.pop("observation_id", "") or "")
        observation = ProofIdeaObservation.create(
            proof_idea_id=idea_id,
            occurrence_key=occurrence_key,
            **observation_content,
        )
        branch_id = str(observation.branch_id or "").strip()
        branches = existing.branch_provenance
        if branch_id and branch_id not in {
            item.branch_id for item in branches
        }:
            branches = branches + (
                ProofIdeaBranchProvenance(
                    branch_id=branch_id,
                    source=str(branch_source or "mini_prover"),
                ),
            )
        updated = replace(
            existing,
            observations=existing.observations + (observation,),
            branch_provenance=branches,
        )
        self.upsert_proof_idea(updated)
        return True

    def record_proof_idea_turn_record(self, record: Mapping[str, Any]) -> int:
        """Reduce child/session tool discoveries into conserved idea memory."""

        payload = dict(record or {})
        idea_id = ""
        route_id = ""
        for candidate in (
            payload,
            payload.get("metadata"),
            payload.get("selected_work"),
        ):
            if not isinstance(candidate, Mapping):
                continue
            try:
                envelope = ProofLineageEnvelope.from_metadata(candidate)
            except (TypeError, ValueError):
                continue
            if envelope.proof_idea_id in self.proof_ideas:
                idea_id = envelope.proof_idea_id
                route_id = envelope.route_id
                break
        if not idea_id and self.proof_graph is not None:
            root = self.proof_graph.nodes.get(self.proof_graph.root_node_id)
            try:
                root_lineage = ProofLineageEnvelope.from_metadata(
                    getattr(root, "metadata", {}) if root is not None else {}
                )
            except (TypeError, ValueError):
                root_lineage = ProofLineageEnvelope()
            if root_lineage.proof_idea_id in self.proof_ideas:
                idea_id = root_lineage.proof_idea_id
                route_id = root_lineage.route_id
        if (
            not idea_id
            and self.proof_idea_singleton_child_scope
            and len(self.proof_ideas) == 1
        ):
            # Child dossiers are seeded with only their relevant idea. This is
            # descriptive correlation, never proof authority.
            idea_id = next(iter(self.proof_ideas))
            singleton = self.proof_ideas[idea_id]
            if len(singleton.consumer_ids) == 1:
                route_id = singleton.consumer_ids[0]
        idea = self.proof_ideas.get(idea_id)
        if idea is None:
            return 0
        branch_id = idea.branch_provenance[0].branch_id
        turn_index = int(
            payload.get("conv_turn_absolute", payload.get("turn_in_phase", 0))
            or 0
        )
        added = 0
        for index, raw_tool in enumerate(payload.get("tool_call_log") or []):
            if not isinstance(raw_tool, Mapping):
                continue
            tool_name = str(raw_tool.get("name") or "").strip()
            full_result = str(
                raw_tool.get("result") or raw_tool.get("result_text") or ""
            ).strip()
            result_preview = str(raw_tool.get("result_preview") or "").strip()
            result_text = full_result or result_preview
            if not tool_name or not result_text:
                continue
            if tool_name in {
                "search_mathlib",
                "check_decl",
                "apply_decl_to_goal",
            }:
                kind = "theorem_discovery"
            elif tool_name in {"try_lean", "check_lean", "try_skeleton"}:
                kind = "lean_residual"
            else:
                continue
            discovered_theorem_names = set(
                re.findall(
                    r"\b(?:[A-Za-z_][A-Za-z0-9_']*\.)+"
                    r"[A-Za-z_][A-Za-z0-9_']*\b",
                    result_text,
                )
            )
            for pattern in (
                r"(?im)^\s*#check\s+([A-Za-z_][A-Za-z0-9_'.]*)\b",
                r"(?im)^\s*\d+[.)]\s+([A-Za-z_][A-Za-z0-9_'.]*)\b",
                r"(?im)\b(?:candidate|declaration|theorem|lemma|name)"
                r"\s*[:=]\s*([A-Za-z_][A-Za-z0-9_'.]*)\b",
            ):
                discovered_theorem_names.update(re.findall(pattern, result_text))
            theorem_names = tuple(sorted(discovered_theorem_names))
            raw_result_length = raw_tool.get("result_length")
            result_length = (
                int(raw_result_length)
                if isinstance(raw_result_length, int)
                and not isinstance(raw_result_length, bool)
                and raw_result_length >= 0
                else len(result_text)
            )
            output_truncated = bool(
                not full_result
                and result_preview
                and result_length > len(result_preview)
            )
            raw_result_sha256 = str(
                raw_tool.get("result_sha256") or ""
            ).strip().lower()
            result_sha256 = (
                raw_result_sha256
                if re.fullmatch(r"[0-9a-f]{64}", raw_result_sha256)
                else ""
            )
            raw_args = raw_tool.get("args")
            attempted_lean_code = (
                str(raw_args.get("code") or "").strip()
                if isinstance(raw_args, Mapping)
                else ""
            )
            observation_id = stable_identity(
                "proof-idea-tool-observation",
                idea_id,
                str(raw_tool.get("tool_call_id") or ""),
                tool_name,
                text_hash(result_text),
                index,
            )
            before = len(self.proof_ideas[idea_id].observations)
            self.record_proof_idea_observation(
                idea_id,
                ProofIdeaObservation(
                    observation_id=observation_id,
                    kind=kind,
                    summary="/".join(
                        value
                        for value in (
                            tool_name,
                            str(raw_tool.get("execution_status") or "").strip(),
                        )
                        if value
                    ),
                    route_id=route_id,
                    exact_lean_output="" if output_truncated else result_text,
                    lean_output_preview=(result_preview if output_truncated else ""),
                    attempted_lean_code=attempted_lean_code,
                    result_sha256=result_sha256,
                    result_length=result_length,
                    output_truncated=output_truncated,
                    theorem_names=theorem_names,
                    evidence_hash=result_sha256 or text_hash(result_text),
                    branch_id=branch_id,
                    turn_index=max(0, turn_index),
                ),
                branch_source="mini_session_tool_turn",
            )
            added += int(len(self.proof_ideas[idea_id].observations) > before)
        return added

    def reconcile_proof_attempt_lineage(self) -> int:
        """Project graph attempts into the append-only lineage ledger.

        Graph callers are intentionally usable without a dossier reference.
        This reducer closes that ownership gap idempotently before scheduling,
        prompt rendering, persistence, or census export.
        """

        graph = self.proof_graph
        if graph is None:
            return 0
        added = 0
        for attempt in list(getattr(graph, "attempts", ()) or ()):
            metadata = dict(getattr(attempt, "metadata", {}) or {})
            try:
                envelope = ProofLineageEnvelope.from_metadata(metadata)
            except (TypeError, ValueError):
                # Pre-schema checkpoints may contain a valid embedded
                # envelope plus malformed legacy mirrors. Preserve valid
                # authority, clear invalid mirrors, and fall back to the graph
                # node lineage rather than crashing prompt rendering/resume.
                sanitized = dict(metadata)
                for field_name in ProofLineageEnvelope.__dataclass_fields__:
                    if field_name in sanitized and not isinstance(
                        sanitized[field_name],
                        str,
                    ):
                        sanitized.pop(field_name, None)
                try:
                    envelope = ProofLineageEnvelope.from_metadata(sanitized)
                except (TypeError, ValueError):
                    sanitized.pop("proof_lineage", None)
                    node = getattr(graph, "nodes", {}).get(
                        str(getattr(attempt, "node_id", "") or "")
                    )
                    try:
                        envelope = ProofLineageEnvelope.from_metadata(
                            getattr(node, "metadata", {}) if node is not None else {}
                        )
                    except (TypeError, ValueError):
                        envelope = ProofLineageEnvelope()
                metadata = sanitized
            if not envelope.proof_candidate_id:
                from ensemble_prover.proof_lineage import proof_candidate_identity

                envelope = envelope.updated(
                    proof_candidate_id=proof_candidate_identity(
                        target_id=str(getattr(attempt, "node_id", "") or ""),
                        proof_hash=str(getattr(attempt, "proof_hash", "") or ""),
                    )
                )
            verdict = str(getattr(attempt, "verdict", "") or "")
            error_type = str(getattr(attempt, "error_type", "") or "")
            if (
                not envelope.lean_residual_id
                and error_type
                and verdict not in {"accepted", "solved", "proved"}
            ):
                from ensemble_prover.proof_lineage import lean_residual_identity

                envelope = envelope.updated(
                    lean_residual_id=lean_residual_identity(
                        proof_candidate_id=envelope.proof_candidate_id,
                        error_type=error_type,
                        failure_signature=str(
                            metadata.get("lean_failure_signature")
                            or metadata.get("failure_signature")
                            or ""
                        ),
                        proof_attempt_id=str(
                            getattr(attempt, "attempt_id", "") or ""
                        ),
                        target_id=str(
                            getattr(attempt, "node_id", "") or ""
                        ),
                    )
                )
            attempt.metadata.update(envelope.merged_metadata(metadata))
            before = len(self.proof_lineage_events)
            self.record_proof_lineage_event(
                event_type="proof_attempt_recorded",
                envelope=envelope,
                phase=str(getattr(attempt, "phase", "") or ""),
                verdict=verdict,
                evidence_hash=str(getattr(attempt, "proof_hash", "") or ""),
                details={
                    "proof_attempt_id": str(
                        getattr(attempt, "attempt_id", "") or ""
                    ),
                    "node_id": str(getattr(attempt, "node_id", "") or ""),
                    "error_type": error_type,
                },
            )
            if envelope.proof_idea_id in self.proof_ideas:
                idea = self.proof_ideas[envelope.proof_idea_id]
                exact_lean_output = next(
                    (
                        str(metadata.get(key) or "")
                        for key in (
                            "exact_lean_output",
                            "lean_output",
                            "error_output",
                            "remaining_goals",
                            "lean_error",
                        )
                        if str(metadata.get(key) or "").strip()
                    ),
                    "",
                )
                theorem_names = tuple(
                    str(value or "").strip()
                    for value in (
                        list(metadata.get("theorem_names") or [])
                        if isinstance(metadata.get("theorem_names"), (list, tuple))
                        else [metadata.get("decl_name")]
                    )
                    if str(value or "").strip()
                )
                branch_id = (
                    str(metadata.get("branch_id") or "").strip()
                    or idea.branch_provenance[0].branch_id
                )
                self.record_proof_idea_observation(
                    envelope.proof_idea_id,
                    ProofIdeaObservation(
                        observation_id=stable_identity(
                            "proof-idea-observation",
                            envelope.proof_idea_id,
                            str(getattr(attempt, "attempt_id", "") or ""),
                        ),
                        kind=(
                            "lean_residual"
                            if envelope.lean_residual_id or error_type
                            else "child_attempt"
                        ),
                        summary="/".join(
                            value
                            for value in (verdict or "attempt", error_type)
                            if value
                        ),
                        claim_id=envelope.claim_id,
                        route_id=envelope.route_id,
                        attempt_id=str(
                            getattr(attempt, "attempt_id", "") or ""
                        ),
                        proof_candidate_id=envelope.proof_candidate_id,
                        lean_residual_id=envelope.lean_residual_id,
                        exact_lean_output=exact_lean_output,
                        theorem_names=theorem_names,
                        evidence_hash=str(
                            getattr(attempt, "proof_hash", "") or ""
                        ),
                        branch_id=branch_id,
                        turn_index=int(
                            getattr(attempt, "turn_index", 0) or 0
                        ),
                    ),
                )
            added += int(len(self.proof_lineage_events) > before)
        return added

    def reconcile_proof_idea_graph_statuses(self) -> int:
        """Reduce authoritative graph route state into idea lifecycle events.

        A proof idea may have several route consumers (for example, repeated
        planner passes). One failed consumer therefore cannot abandon the
        mathematical strategy while another remains live. Lean success on any
        consumer is conclusive; negative/retirement states become idea-level
        only when every known consumer is terminal in the corresponding way.
        """

        graph = self.proof_graph
        if graph is None:
            return 0
        added = 0
        terminal_statuses = {"failed", "rejected", "superseded", "invalidated"}
        for idea_id, idea in list(self.proof_ideas.items()):
            routes = [
                graph.nodes[route_id]
                for route_id in idea.consumer_ids
                if route_id in graph.nodes
                and graph.nodes[route_id].kind == "strategy_route"
            ]
            if not routes:
                continue

            classified: List[Tuple[Any, str, str]] = []
            for route in routes:
                metadata = dict(getattr(route, "metadata", {}) or {})
                status = str(getattr(route, "status", "") or "").strip()
                proof_hash = str(
                    getattr(route, "proof_hash", "")
                    or metadata.get("assembled_route_proof_hash")
                    or ""
                ).strip()
                authority_ids = [
                    str(item or "").strip()
                    for item in list(
                        metadata.get(
                            "authoritative_falsification_authority_ids"
                        )
                        or []
                    )
                    if str(item or "").strip()
                    in self.mini_authoritative_negations
                ]
                if authority_ids:
                    authority = self.mini_authoritative_negations[
                        sorted(authority_ids)[0]
                    ]
                    evidence_id = str(
                        authority.get("certificate_hash")
                        or authority.get("report_hash")
                        or authority.get("authority_id")
                    ).strip()
                    classified.append((route, "invalidated", evidence_id))
                elif status == "proved" and proof_hash:
                    classified.append((route, "solved", proof_hash))
                elif metadata.get("route_retired") or metadata.get(
                    "route_dependency_contradicted"
                ):
                    classified.append(
                        (
                            route,
                            (
                                "retired"
                                if metadata.get(
                                    "partial_route_fulfilled_by_verified_fact"
                                )
                                else "abandoned"
                            ),
                            "",
                        )
                    )
                elif status == "superseded":
                    classified.append((route, "retired", ""))
                elif status in terminal_statuses:
                    classified.append((route, "abandoned", ""))
                elif status == "blocked":
                    classified.append((route, "blocked", ""))
                else:
                    classified.append((route, "active", ""))

            solved = [item for item in classified if item[1] == "solved"]
            if solved:
                route, next_status, evidence_id = max(
                    solved,
                    key=lambda item: (
                        int(getattr(item[0], "turn_index", 0) or 0),
                        item[0].node_id,
                    ),
                )
                authority = "lean"
                reason = "Lean-certified route consumer solved the proof idea"
            elif all(item[1] == "invalidated" for item in classified):
                route, next_status, evidence_id = max(
                    classified,
                    key=lambda item: (
                        int(getattr(item[0], "turn_index", 0) or 0),
                        item[0].node_id,
                    ),
                )
                authority = "lean"
                reason = "every route consumer has authoritative falsification evidence"
            elif all(item[1] == "retired" for item in classified):
                route, next_status, evidence_id = max(
                    classified,
                    key=lambda item: (
                        int(getattr(item[0], "turn_index", 0) or 0),
                        item[0].node_id,
                    ),
                )
                authority = "controller"
                reason = "every route consumer is superseded or fulfilled"
            elif all(
                item[1] in {"abandoned", "invalidated", "retired"}
                for item in classified
            ):
                route, _route_state, _evidence = max(
                    classified,
                    key=lambda item: (
                        int(getattr(item[0], "turn_index", 0) or 0),
                        item[0].node_id,
                    ),
                )
                next_status = "abandoned"
                evidence_id = ""
                authority = "controller"
                reason = "every route consumer is retired or rejected"
            elif any(item[1] == "blocked" for item in classified) and all(
                item[1] in {"blocked", "abandoned", "invalidated", "retired"}
                for item in classified
            ):
                route, next_status, evidence_id = max(
                    classified,
                    key=lambda item: (
                        int(getattr(item[0], "turn_index", 0) or 0),
                        item[0].node_id,
                    ),
                )
                authority = "controller"
                reason = "every live route consumer is blocked"
            else:
                route, _route_state, _evidence = max(
                    classified,
                    key=lambda item: (
                        int(getattr(item[0], "turn_index", 0) or 0),
                        item[0].node_id,
                    ),
                )
                next_status = "active"
                evidence_id = ""
                authority = "controller"
                reason = "at least one route consumer is active"

            # Route-derived status belongs to the route's actual branch.  A
            # blank route branch is an explicit global lifecycle scope; it is
            # not permission to forge the first branch listed on the idea.
            branch_id = str(
                (getattr(route, "metadata", {}) or {}).get("branch_id") or ""
            ).strip()
            current = idea.current_status_transition
            authority_rank = {
                "advisory": 0,
                "controller": 1,
                "accepted_fact": 2,
                "lean": 3,
            }
            if current.effective_authority_rank > authority_rank[authority]:
                continue
            if (
                current.status == next_status
                and current.authority == authority
                and current.evidence_id == evidence_id
            ):
                continue
            transition_turn = max(
                0, int(getattr(route, "turn_index", 0) or 0)
            )
            if (
                current.effective_authority_rank == authority_rank[authority]
                and transition_turn <= current.turn_index
            ):
                transition_turn = current.turn_index + 1
            transition = ProofIdeaStatusTransition.create(
                proof_idea_id=idea_id,
                occurrence_key=route.node_id,
                status=next_status,
                authority=authority,
                reason=reason,
                turn_index=transition_turn,
                route_id=route.node_id,
                branch_id=branch_id,
                evidence_id=evidence_id,
            )
            before = len(idea.status_history)
            self.upsert_proof_idea(
                replace(idea, status_history=idea.status_history + (transition,))
            )
            idea = self.proof_ideas[idea_id]
            added += int(len(idea.status_history) > before)
        return added

    def render_active_strategy_context(
        self,
        *,
        max_routes: int = 2,
        max_open_siblings: int = 3,
    ) -> str:
        """Render the concise, durable route lifecycle—not graph narration."""

        graph = self.proof_graph
        if graph is None:
            return ""
        self.reconcile_proof_attempt_lineage()
        self.reconcile_proof_idea_graph_statuses()
        prompt_hidden_helper_names = {
            str(name or "").strip()
            for name, helper in self.verified_helpers.items()
            if str(name or "").strip()
            and not self._verified_helper_context_visible(helper)
        }
        prompt_hidden_helper_node_ids = {
            str(graph.helper_name_to_node_id.get(name) or "").strip()
            for name in prompt_hidden_helper_names
            if str(graph.helper_name_to_node_id.get(name) or "").strip()
        }

        def lifecycle_prompt_text(value: Any, *, limit: int) -> str:
            text = _prompt_safe_inline_text(
                str(value or ""),
                limit=limit,
                redact_solution_refs=True,
            )
            for hidden_name in prompt_hidden_helper_names:
                if len(hidden_name) >= 12:
                    text = text.replace(hidden_name, "[hidden-helper]")
                elif text == hidden_name:
                    text = "[hidden-helper]"
            return text

        routes = []
        for route in graph.nodes_by_kind("strategy_route"):
            metadata = dict(getattr(route, "metadata", {}) or {})
            if str(getattr(route, "status", "") or "") in {
                "proved",
                "invalidated",
                "superseded",
            }:
                continue
            if metadata.get("route_retired") or metadata.get(
                "route_dependency_contradicted"
            ):
                continue
            dependency_ids = [
                edge.target
                for edge in graph.edges
                if edge.source == route.node_id
                and str(edge.kind or "").startswith("route_")
            ]
            route_prompt_fields = (
                str(getattr(route, "name", "") or ""),
                str(getattr(route, "statement", "") or ""),
                str(metadata.get("strategy") or ""),
                str(metadata.get("claim_name") or ""),
            )
            if (
                prompt_hidden_helper_node_ids.intersection(dependency_ids)
                or any(
                    hidden_name == field
                    or (len(hidden_name) >= 12 and hidden_name in field)
                    for hidden_name in prompt_hidden_helper_names
                    for field in route_prompt_fields
                )
            ):
                # Advisory negative evidence and other prompt-hidden helpers
                # must not re-enter the prompt through dependency edges or a
                # generated route name.  Require exact fields for short names
                # to avoid suppressing every route merely because a hidden
                # helper happened to be named ``h``.
                continue
            dependencies = [
                graph.nodes[node_id]
                for node_id in dict.fromkeys(dependency_ids)
                if node_id in graph.nodes
            ]
            open_dependencies = [
                node
                for node in dependencies
                if str(getattr(node, "status", "") or "") != "proved"
            ]
            score = float(metadata.get("score", 0.0) or 0.0)
            route_scope = str(metadata.get("route_scope") or "").strip()
            routes.append(
                (
                    0 if route_scope == "root_assembly" else 1,
                    len(open_dependencies),
                    -score,
                    -int(getattr(route, "turn_index", 0) or 0),
                    route,
                    open_dependencies,
                    len(dependencies),
                )
            )
        if not routes:
            return ""
        routes.sort(key=lambda item: item[:4])
        lines = ["- active proof strategy lineage:"]
        for _, _, _, _, route, open_dependencies, dependency_count in routes[
            : max(1, int(max_routes or 1))
        ]:
            metadata = dict(getattr(route, "metadata", {}) or {})
            lineage = ProofLineageEnvelope.from_metadata(metadata)
            route_label = _prompt_safe_inline_text(
                str(getattr(route, "name", "") or route.node_id),
                limit=120,
                redact_solution_refs=True,
            )
            strategy = _prompt_safe_inline_text(
                str(
                    metadata.get("strategy")
                    or getattr(route, "statement", "")
                    or ""
                ),
                limit=220,
                redact_solution_refs=True,
            )
            strategy_id = (
                lineage.strategy_lineage_id[-12:]
                if lineage.strategy_lineage_id
                else "unassigned"
            )
            lines.append(
                f"  - route `{route_label}` (lineage {strategy_id}) consumes "
                f"{dependency_count} AND-dependenc{'y' if dependency_count == 1 else 'ies'}; "
                f"{len(open_dependencies)} remain open"
                + (f"; idea: {strategy}" if strategy else "")
            )
            proof_idea = self.proof_ideas.get(lineage.proof_idea_id)
            if proof_idea is not None:
                notes = lifecycle_prompt_text(
                    "; ".join(proof_idea.notes),
                    limit=260,
                )
                if notes:
                    lines.append(f"    - advisory route memory: {notes}")
                relevant_claim_ids = {
                    node.node_id for node in open_dependencies
                }
                relevant_claim_ids.update(
                    lineage.claim_id
                    for node in open_dependencies
                    for lineage in [
                        ProofLineageEnvelope.from_metadata(
                            getattr(node, "metadata", {}) or {}
                        )
                    ]
                    if lineage.claim_id
                )
                relevant_intents = [
                    intent
                    for intent in proof_idea.claim_intents
                    if route.node_id in intent.consumer_ids
                    and (
                        not relevant_claim_ids
                        or intent.claim_id in relevant_claim_ids
                    )
                ]
                for intent in relevant_intents[: max(1, int(max_open_siblings or 1))]:
                    rationale = lifecycle_prompt_text(
                        intent.rationale,
                        limit=240,
                    )
                    alternatives = lifecycle_prompt_text(
                        "; ".join(
                            intent.rationale_alternatives
                            + intent.alternative_statements
                        ),
                        limit=220,
                    )
                    if rationale or alternatives:
                        lines.append(
                            "    - claim intent"
                            + (f": {rationale}" if rationale else "")
                            + (
                                f"; prior formulations: {alternatives}"
                                if alternatives
                                else ""
                            )
                        )
                scoped_observations = [
                    observation
                    for observation in proof_idea.observations
                    if observation.route_id == route.node_id
                    or (
                        not observation.route_id
                        and observation.claim_id in relevant_claim_ids
                    )
                    or (
                        not observation.route_id
                        and not observation.claim_id
                        and len(proof_idea.consumer_ids) == 1
                    )
                ]
                if scoped_observations:
                    latest_observation = max(
                        scoped_observations,
                        key=lambda item: (item.turn_index, item.observation_id),
                    )
                    observation_summary = lifecycle_prompt_text(
                        latest_observation.summary,
                        limit=180,
                    )
                    exact_output = lifecycle_prompt_text(
                        latest_observation.exact_lean_output,
                        limit=360,
                    )
                    output_preview = lifecycle_prompt_text(
                        latest_observation.lean_output_preview,
                        limit=360,
                    )
                    attempted_code = lifecycle_prompt_text(
                        latest_observation.attempted_lean_code,
                        limit=360,
                    )
                    theorem_names = lifecycle_prompt_text(
                        ", ".join(latest_observation.theorem_names),
                        limit=180,
                    )
                    lines.append(
                        "    - latest conserved observation: "
                        f"{latest_observation.kind}"
                        + (f"/{observation_summary}" if observation_summary else "")
                        + (f"; near theorems: {theorem_names}" if theorem_names else "")
                        + (f"; exact Lean residual: {exact_output}" if exact_output else "")
                        + (
                            "; Lean residual preview (truncated"
                            + (
                                f", sha256 {latest_observation.result_sha256}"
                                if latest_observation.result_sha256
                                else ""
                            )
                            + (
                                f", original chars {latest_observation.result_length}"
                                if latest_observation.result_length
                                else ""
                            )
                            + f"): {output_preview}"
                            if output_preview
                            else ""
                        )
                        + (
                            f"; attempted Lean: {attempted_code}"
                            if attempted_code
                            else ""
                        )
                    )
                    provenance = "/".join(
                        value
                        for value in (
                            (
                                f"pass {latest_observation.source_pass_index}"
                                if latest_observation.source_pass_index
                                else ""
                            ),
                            latest_observation.source_trigger,
                            latest_observation.source_model_id,
                        )
                        if value
                    )
                    if provenance:
                        lines.append(
                            "    - observation provenance: "
                            + lifecycle_prompt_text(provenance, limit=180)
                        )
            for node in open_dependencies[: max(1, int(max_open_siblings or 1))]:
                statement = _prompt_safe_inline_text(
                    str(getattr(node, "statement", "") or ""),
                    limit=260,
                    redact_solution_refs=True,
                )
                sibling_name = str(getattr(node, "name", "") or node.node_id)
                for hidden_name in prompt_hidden_helper_names:
                    if not hidden_name:
                        continue
                    if len(hidden_name) >= 12:
                        statement = statement.replace(hidden_name, "[hidden-helper]")
                        sibling_name = sibling_name.replace(
                            hidden_name, "[hidden-helper]"
                        )
                    else:
                        if statement == hidden_name:
                            statement = "[hidden-helper]"
                        if sibling_name == hidden_name:
                            sibling_name = "[hidden-helper]"
                lines.append(
                    f"    - next sibling `{sibling_name}`: "
                    f"`{statement or '(formalization pending)'}`"
                )
            route_attempts = [
                attempt
                for attempt in graph.attempts
                if str(getattr(attempt, "node_id", "") or "") == route.node_id
            ]
            related_attempts = route_attempts or [
                attempt
                for attempt in graph.attempts
                if str(getattr(attempt, "node_id", "") or "")
                in {node.node_id for node in open_dependencies}
            ]
            if related_attempts:
                last = related_attempts[-1]
                last_lineage = ProofLineageEnvelope.from_metadata(last.metadata)
                residual = (
                    last_lineage.lean_residual_id[-12:]
                    if last_lineage.lean_residual_id
                    else "none"
                )
                lines.append(
                    "    - latest route attempt: "
                    f"{str(last.verdict or 'attempt')}"
                    + (
                        f"/{str(last.error_type)}"
                        if str(last.error_type or "")
                        else ""
                    )
                    + f"; residual {residual}"
                )
        return "\n".join(lines)

    @staticmethod
    def _graph_node_contract_identity(node: Any) -> str:
        return graph_node_bound_contract_identity(node)

    def _verified_fact_identity(self, helper: VerifiedHelper) -> str:
        """Return the mathematical proposition identity for one attestation.

        A fact is the proposition Lean elaborated in one exact environment.
        How a particular helper proved that proposition is attestation
        provenance, not part of the proposition identity.  In particular,
        support hashes must not split one accepted fact merely because it was
        reproved through a different route.
        """

        statement = helper_decl_statement(helper.source)
        contract_identity = verified_helper_bound_contract_identity(helper)
        parsed_identity = parse_lean_contract_identity(contract_identity)
        statement_identity = (
            stable_identity("lean-full-expression", parsed_identity[0])
            if parsed_identity is not None
            else structural_statement_identity(
                statement,
                contract_identity=contract_identity,
                statement_key=canonical_dossier_statement_key(statement),
            )
        )
        environment_hash = str(
            helper.verification_environment_hash or ""
        ).strip()
        # Preserve the legacy identifier for the single exact "unknown"
        # environment partition. Dependency provenance no longer changes it.
        if not environment_hash:
            return statement_identity
        return stable_identity(
            "verified-fact",
            statement_identity,
            environment_hash,
        )

    @staticmethod
    def _verified_fact_attestation(helper: VerifiedHelper) -> Dict[str, Any]:
        """Capture proof-specific evidence without changing fact identity."""

        return {
            "schema_version": 1,
            "helper_name": str(helper.name or ""),
            "source_hash": str(helper.source_hash or ""),
            "phase": str(helper.phase or ""),
            "turn_index": int(helper.turn_index or 0),
            "verification_environment_hash": str(
                helper.verification_environment_hash or ""
            ).strip(),
            "support_names": [
                str(name or "").strip()
                for name in list(helper.support_names or [])
                if str(name or "").strip()
            ],
            "support_source_hashes": {
                str(name or "").strip(): str(source_hash or "").strip()
                for name, source_hash in dict(
                    helper.support_source_hashes or {}
                ).items()
                if str(name or "").strip()
                and str(source_hash or "").strip()
            },
            "replay_context_names": [
                str(name or "").strip()
                for name in list(helper.replay_context_names or [])
                if str(name or "").strip()
            ],
            "replay_context_source_hashes": {
                str(name or "").strip(): str(source_hash or "").strip()
                for name, source_hash in dict(
                    helper.replay_context_source_hashes or {}
                ).items()
                if str(name or "").strip()
                and str(source_hash or "").strip()
            },
            "provenance_tags": [
                str(tag or "").strip()
                for tag in list(helper.provenance_tags or [])
                if str(tag or "").strip()
            ],
            "visibility_policy": str(helper.visibility_policy or ""),
            "render_policy": str(helper.render_policy or ""),
            "quality_tags": [
                str(tag or "").strip()
                for tag in list(helper.quality_tags or [])
                if str(tag or "").strip()
            ],
            "open_premise_statement_keys": list(
                helper.open_premise_statement_keys or []
            ),
            "contract_identity": verified_helper_bound_contract_identity(helper),
            "contract_identity_statement_key": str(
                helper.contract_identity_statement_key or ""
            ),
            "contract_identity_environment_hash": str(
                helper.contract_identity_environment_hash or ""
            ),
            "contract_identity_evidence_receipt": str(
                helper.contract_identity_evidence_receipt or ""
            ),
            "contract_display_statement": str(
                helper.contract_display_statement or ""
            ),
            "contract_binder_sorts": list(helper.contract_binder_sorts or []),
            "contract_proof_binder_types": list(
                helper.contract_proof_binder_types or []
            ),
        }

    def _rebuild_semantic_fact_registry(
        self,
        *,
        preserve_history: bool = True,
    ) -> None:
        """Atomically rebuild live facts from the authoritative helper set.

        Helper membership and proof attestations are derived state.  Rebuilding
        them in a fresh mapping prevents evidence upgrades, replacements, and
        removals from leaving a formerly valid receipt live.  Cumulative graph
        retirement history remains attached only when the same proposition
        identity is still attested.
        """

        previous = self.semantic_fact_registry if preserve_history else {}
        rebuilt: Dict[str, Dict[str, Any]] = {}
        history_fields = (
            "resolved_node_ids",
            "newly_ready_route_ids",
            "route_readiness_evidence",
            "reconciliation_count",
        )
        for helper in self.verified_helpers.values():
            fact_id = self._verified_fact_identity(helper)
            if not fact_id:
                continue
            statement = helper_decl_statement(helper.source)
            statement_key = canonical_dossier_statement_key(statement)
            contract_identity = verified_helper_bound_contract_identity(helper)
            receipt = rebuilt.get(fact_id)
            if receipt is None:
                receipt = {
                    "schema_version": 2,
                    "fact_id": fact_id,
                    "statement": statement,
                    "statement_key": statement_key,
                    "contract_identity": contract_identity,
                    "helper_names": [],
                    "helper_source_hashes": {},
                    "statements_by_helper": {},
                    "statement_keys_by_helper": {},
                    "base_environment_hash": str(
                        self.graph_execution_project_environment_hash or ""
                    ),
                    "verification_environment_hashes": [],
                    # Compatibility aggregate. Exact proof-route provenance is
                    # owned by the per-helper attestations below.
                    "dependency_source_hashes": {},
                    "attestations": {},
                    "resolved_node_ids": [],
                    "newly_ready_route_ids": [],
                    "reconciliation_count": 0,
                }
                old_receipt = previous.get(fact_id)
                if isinstance(old_receipt, dict):
                    for field_name in history_fields:
                        if field_name in old_receipt:
                            receipt[field_name] = copy.deepcopy(
                                old_receipt[field_name]
                            )
                rebuilt[fact_id] = receipt
            helper_name = str(helper.name or "")
            if helper_name not in receipt["helper_names"]:
                receipt["helper_names"].append(helper_name)
            receipt["helper_source_hashes"][helper_name] = str(
                helper.source_hash or ""
            )
            receipt["statements_by_helper"][helper_name] = statement
            receipt["statement_keys_by_helper"][helper_name] = statement_key
            receipt["attestations"][helper_name] = (
                self._verified_fact_attestation(helper)
            )
            verification_hash = str(
                helper.verification_environment_hash or ""
            ).strip()
            if (
                verification_hash
                and verification_hash
                not in receipt["verification_environment_hashes"]
            ):
                receipt["verification_environment_hashes"].append(
                    verification_hash
                )
            receipt["dependency_source_hashes"].update(
                receipt["attestations"][helper_name]["support_source_hashes"]
            )
        self.semantic_fact_registry = rebuilt

    def _ready_route_ids(self) -> Set[str]:
        graph = self.proof_graph
        if graph is None:
            return set()
        ready: Set[str] = set()
        for route in graph.nodes_by_kind("strategy_route"):
            try:
                # Readiness probes used by fact reconciliation must not mutate
                # route contracts. The mutable status path clears branch frames
                # for incomplete/imported routes and would destroy structural
                # fan-in work that reconcile is supposed to leave intact.
                status = graph.route_assembly_contract_status(
                    route.node_id,
                    mutate=False,
                )
            except Exception:
                continue
            if bool(status.get("ready")):
                ready.add(route.node_id)
        return ready

    def _proof_idea_fact_consumers(
        self,
        node_ids: Iterable[str],
    ) -> Dict[str, Dict[str, Any]]:
        """Project fact-derived graph nodes to all cognition consumers."""

        graph = self.proof_graph
        consumers: Dict[str, Dict[str, Any]] = {}
        if graph is None:
            return consumers
        for node_id in sorted(
            {
                str(value or "").strip()
                for value in node_ids
                if str(value or "").strip()
            }
        ):
            node = graph.nodes.get(node_id)
            if node is None:
                continue
            work_record = {
                "claim_id": node.node_id if node.kind == "proposed_claim" else ""
            }
            for raw_binding in graph.consumer_bindings_for_node(
                node.node_id,
                work_record,
            ):
                binding = self._proof_idea_binding_from_packet(raw_binding)
                idea = self.proof_ideas.get(binding.proof_idea_id)
                if idea is None:
                    continue
                intent_ids = {intent.claim_id for intent in idea.claim_intents}
                matching_claim_ids = {
                    candidate
                    for candidate in (binding.claim_id, node.node_id)
                    if candidate in intent_ids
                }
                node_identity = (
                    binding.statement_identity
                    or structural_statement_identity(
                        node.statement,
                        contract_identity=self._graph_node_contract_identity(node),
                        statement_key=canonical_dossier_statement_key(
                            node.statement
                        ),
                    )
                )
                matching_claim_ids.update(
                    intent.claim_id
                    for intent in idea.claim_intents
                    if node_identity
                    and node_identity
                    in {
                        intent.statement_identity,
                        *intent.alternative_statement_identities,
                    }
                )
                if not matching_claim_ids:
                    continue
                entry = consumers.setdefault(
                    idea.proof_idea_id,
                    {"claims": {}, "branches": set()},
                )
                for claim_id in matching_claim_ids:
                    entry["claims"].setdefault(claim_id, set()).add(node.node_id)
                if binding.branch_id:
                    entry["branches"].add(binding.branch_id)
        return consumers

    def _restore_stale_fact_archives(self) -> List[str]:
        """Undo route state derived from facts that no longer have attestation."""

        graph = self.proof_graph
        if graph is None:
            return []
        restored: List[str] = []
        active_fact_ids = set(self.semantic_fact_registry)
        for route in graph.nodes_by_kind("strategy_route"):
            metadata = dict(route.metadata or {})
            if not metadata.get("partial_route_fulfilled_by_verified_fact"):
                continue
            retired_fact_ids = {
                str(value or "").strip()
                for value in list(metadata.get("fulfilled_verified_fact_ids") or [])
                if str(value or "").strip()
            }
            if retired_fact_ids and retired_fact_ids.issubset(active_fact_ids):
                continue
            snapshot = metadata.pop("verified_fact_archive_snapshot", None)
            history = list(metadata.get("verified_fact_archive_history") or [])
            history.append(
                {
                    "fulfilled_verified_fact_ids": sorted(retired_fact_ids),
                    "eviction_generation": int(
                        self.verified_helper_eviction_generation or 0
                    ),
                }
            )
            metadata["verified_fact_archive_history"] = history
            still_fact_archived = bool(
                route.status == "superseded"
                and str(metadata.get("route_retirement_verdict") or "")
                == "partial_route_fulfilled"
            )
            if isinstance(snapshot, Mapping):
                # Restore the archived status only while the route still bears
                # the exact fact-derived tombstone. A newer controller status
                # (blocked/abandoned/reactivated) is later authority and must
                # not be clobbered by this stale snapshot.
                if still_fact_archived:
                    route.status = str(snapshot.get("status") or "open")
                    route.proof_hash = str(snapshot.get("proof_hash") or "")
                    route.source_hash = str(snapshot.get("source_hash") or "")
                    prior_activation = snapshot.get("activation_status")
                    if prior_activation in (None, ""):
                        metadata.pop("activation_status", None)
                    else:
                        metadata["activation_status"] = str(prior_activation)
            elif still_fact_archived:
                route.status = "open"
                route.proof_hash = ""
                metadata["activation_status"] = "active"
            for key in (
                "partial_route_fulfilled_by_verified_fact",
                "fulfilled_dependency_node_ids",
                "fulfilled_verified_fact_ids",
            ):
                metadata.pop(key, None)
            for key in (
                "route_retirement_verdict",
                "route_assembly_contract_last_verdict",
            ):
                if str(metadata.get(key) or "") == "partial_route_fulfilled":
                    metadata.pop(key, None)
            route.metadata = metadata
            restored.append(route.node_id)
        return restored

    def _retract_inactive_accepted_fact_lifecycle(self) -> List[str]:
        """Append compensation events for fact-derived lifecycle closures."""

        active_fact_ids = set(self.semantic_fact_registry)
        retracted_idea_ids: List[str] = []
        for idea_id, original in list(self.proof_ideas.items()):
            idea = original
            changed_claim_ids: List[str] = []
            changed_node_ids: Set[str] = set()
            for intent in idea.claim_intents:
                current = idea.current_claim_resolution(intent.claim_id)
                if (
                    current is None
                    or current.authority != "accepted_fact"
                    or current.status not in {"retired", "solved"}
                    or current.evidence_id in active_fact_ids
                ):
                    continue
                active_candidates = [
                    item
                    for item in idea.claim_resolutions
                    if item.claim_id == intent.claim_id
                    and item.authority == "accepted_fact"
                    and item.status in {"retired", "solved"}
                    and item.evidence_id in active_fact_ids
                ]
                next_turn = max(
                    [current.turn_index]
                    + [item.turn_index for item in idea.claim_resolutions]
                ) + 1
                if active_candidates:
                    replacement = max(
                        active_candidates,
                        key=lambda item: (item.turn_index, item.resolution_id),
                    )
                    compensation = ProofIdeaClaimResolution.create(
                        proof_idea_id=idea_id,
                        occurrence_key=(
                            "accepted-fact-rebound:"
                            + str(self.verified_helper_eviction_generation or 0)
                        ),
                        claim_id=intent.claim_id,
                        status=replacement.status,
                        authority="accepted_fact",
                        reason="claim remains retired by a surviving accepted fact",
                        evidence_id=replacement.evidence_id,
                        turn_index=next_turn,
                        node_ids=replacement.node_ids,
                    )
                else:
                    compensation = ProofIdeaClaimResolution.create(
                        proof_idea_id=idea_id,
                        occurrence_key=(
                            "accepted-fact-retracted:"
                            + str(self.verified_helper_eviction_generation or 0)
                        ),
                        claim_id=intent.claim_id,
                        status="retracted",
                        authority="accepted_fact",
                        reason="final accepted-fact attestation was removed",
                        evidence_id=current.evidence_id,
                        turn_index=next_turn,
                        node_ids=current.node_ids,
                    )
                    changed_claim_ids.append(intent.claim_id)
                    changed_node_ids.update(current.node_ids)
                idea = self.upsert_proof_idea(
                    replace(
                        idea,
                        claim_resolutions=idea.claim_resolutions + (compensation,),
                    )
                )
            if not changed_claim_ids:
                continue
            consumers = self._proof_idea_fact_consumers(changed_node_ids).get(
                idea_id, {"branches": set()}
            )
            branches = sorted(consumers.get("branches") or set()) or [""]
            turn_index = max(
                transition.turn_index for transition in idea.status_history
            ) + 1
            for branch_id in branches:
                self.record_proof_idea_observation(
                    idea_id,
                    ProofIdeaObservation.create(
                        proof_idea_id=idea_id,
                        occurrence_key=(
                            "accepted-fact-retracted:"
                            + str(self.verified_helper_eviction_generation or 0)
                            + ":"
                            + branch_id
                        ),
                        kind="evidence_delta",
                        summary=(
                            "accepted-fact retirement was retracted after the "
                            "final attestation was removed"
                        ),
                        branch_id=branch_id,
                        turn_index=turn_index,
                    ),
                )
            idea = self.proof_ideas[idea_id]
            all_closed = all(
                (resolution := idea.current_claim_resolution(intent.claim_id))
                is not None
                and resolution.status in {"retired", "solved"}
                for intent in idea.claim_intents
            )
            current_status = idea.current_status_transition
            if (
                current_status.authority == "accepted_fact"
                and current_status.evidence_id not in active_fact_ids
            ):
                active_evidence = sorted(
                    {
                        resolution.evidence_id
                        for intent in idea.claim_intents
                        if (
                            resolution := idea.current_claim_resolution(
                                intent.claim_id
                            )
                        )
                        is not None
                        and resolution.status in {"retired", "solved"}
                        and resolution.evidence_id in active_fact_ids
                    }
                )
                transition = ProofIdeaStatusTransition.create(
                    proof_idea_id=idea_id,
                    occurrence_key=(
                        "accepted-fact-status-compensation:"
                        + str(self.verified_helper_eviction_generation or 0)
                    ),
                    status="retired" if all_closed else "active",
                    authority="accepted_fact",
                    reason=(
                        "all claims remain fulfilled by live accepted facts"
                        if all_closed
                        else "accepted-fact retirement was retracted"
                    ),
                    turn_index=max(turn_index, current_status.turn_index + 1),
                    evidence_id="|".join(active_evidence),
                )
                self.upsert_proof_idea(
                    replace(
                        idea,
                        status_history=idea.status_history + (transition,),
                    )
                )
            retracted_idea_ids.append(idea_id)
        return retracted_idea_ids

    def _ensure_accepted_fact_lifecycle(
        self,
        *,
        helper: VerifiedHelper,
        fact_id: str,
        node_ids: Iterable[str],
    ) -> None:
        """Converge every current consumer onto one live fact receipt."""

        consumers = self._proof_idea_fact_consumers(node_ids)
        for idea_id, consumer in consumers.items():
            idea = self.proof_ideas[idea_id]
            claims = {
                claim_id: tuple(sorted(node_set))
                for claim_id, node_set in dict(consumer.get("claims") or {}).items()
            }
            all_node_ids = sorted(
                {
                    node_id
                    for claim_nodes in claims.values()
                    for node_id in claim_nodes
                }
            )
            for branch_id in sorted(consumer.get("branches") or set()) or [""]:
                self.record_proof_idea_observation(
                    idea_id,
                    ProofIdeaObservation.create(
                        proof_idea_id=idea_id,
                        occurrence_key=(
                            fact_id + ":" + branch_id + ":" + ":".join(all_node_ids)
                        ),
                        kind="evidence_delta",
                        summary=(
                            f"accepted fact {fact_id} retired equivalent graph work: "
                            + ", ".join(all_node_ids)
                        ),
                        evidence_hash=helper.source_hash,
                        branch_id=branch_id,
                        turn_index=int(helper.turn_index or 0),
                    ),
                )
            idea = self.proof_ideas[idea_id]
            additions: List[ProofIdeaClaimResolution] = []
            for claim_id, claim_node_ids in sorted(claims.items()):
                current = idea.current_claim_resolution(claim_id)
                if (
                    current is not None
                    and current.authority == "accepted_fact"
                    and current.status in {"retired", "solved"}
                    and current.evidence_id == fact_id
                    and set(claim_node_ids).issubset(current.node_ids)
                ):
                    continue
                next_turn = max(
                    int(helper.turn_index or 0),
                    (current.turn_index + 1 if current is not None else 0),
                )
                additions.append(
                    ProofIdeaClaimResolution.create(
                        proof_idea_id=idea_id,
                        occurrence_key=(
                            fact_id
                            + ":converge:"
                            + str(self.verified_helper_eviction_generation or 0)
                        ),
                        claim_id=claim_id,
                        status="retired",
                        authority="accepted_fact",
                        reason="accepted fact retired equivalent graph work",
                        evidence_id=fact_id,
                        turn_index=next_turn,
                        node_ids=claim_node_ids,
                    )
                )
            if additions:
                idea = self.upsert_proof_idea(
                    replace(
                        idea,
                        claim_resolutions=idea.claim_resolutions + tuple(additions),
                    )
                )
            if idea.claim_intents and all(
                (resolution := idea.current_claim_resolution(intent.claim_id))
                is not None
                and resolution.status in {"retired", "solved"}
                for intent in idea.claim_intents
            ):
                current_status = idea.current_status_transition
                if not (
                    current_status.authority == "accepted_fact"
                    and current_status.status == "retired"
                    and current_status.evidence_id == fact_id
                ):
                    self.upsert_proof_idea(
                        replace(
                            idea,
                            status_history=idea.status_history
                            + (
                                ProofIdeaStatusTransition.create(
                                    proof_idea_id=idea_id,
                                    occurrence_key=(
                                        fact_id
                                        + ":converge:"
                                        + str(
                                            self.verified_helper_eviction_generation
                                            or 0
                                        )
                                    ),
                                    status="retired",
                                    authority="accepted_fact",
                                    reason=(
                                        "all claim intents were fulfilled by "
                                        "accepted facts"
                                    ),
                                    turn_index=max(
                                        int(helper.turn_index or 0),
                                        current_status.turn_index + 1,
                                    ),
                                    branch_id="",
                                    evidence_id=fact_id,
                                ),
                            ),
                        )
                    )

    def _archive_fulfilled_partial_routes(self) -> List[str]:
        """Archive telemetry routes whose accepted fact work is complete.

        Mini-recursive claim attempts create ``partial_route`` wrappers so a
        failed claim can retain its obligation and replan lineage.  Those
        wrappers are not root-assembly routes.  Once every dependency is
        durably proved and every required claim is bound to a current semantic
        fact receipt, keeping the wrapper open creates phantom frontier work.

        Root-assembly contracts are deliberately excluded: their proved
        dependencies make them ready for assembly rather than fulfilled.
        """

        graph = self.proof_graph
        if graph is None:
            return []
        archived: List[str] = []
        dependency_edge_kinds = {
            "route_requires",
            "route_blocked_by",
            "route_replan",
        }
        for route in graph.nodes_by_kind("strategy_route"):
            metadata = dict(route.metadata or {})
            if (
                route.status != "open"
                or str(metadata.get("route_scope") or "").strip()
                != "partial_route"
                or isinstance(metadata.get("route_assembly_contract"), dict)
            ):
                continue
            dependency_edges = [
                edge
                for edge in graph.outgoing(route.node_id)
                if edge.kind in dependency_edge_kinds
            ]
            required_edges = [
                edge for edge in dependency_edges if edge.kind == "route_requires"
            ]
            if not required_edges:
                continue
            dependencies = [graph.nodes.get(edge.target) for edge in dependency_edges]
            if not dependencies or not all(
                graph._proved_node_has_durable_certificate(node)
                for node in dependencies
            ):
                continue
            verified_fact_ids = {
                str((node.metadata or {}).get("verified_fact_id") or "").strip()
                for node in (
                    graph.nodes.get(edge.target) for edge in required_edges
                )
                if node is not None
            }
            if (
                not verified_fact_ids
                or "" in verified_fact_ids
                or not all(
                    fact_id in self.semantic_fact_registry
                    for fact_id in verified_fact_ids
                )
            ):
                continue
            route.metadata["verified_fact_archive_snapshot"] = {
                "status": route.status,
                "proof_hash": route.proof_hash,
                "source_hash": route.source_hash,
                "activation_status": route.metadata.get("activation_status"),
            }
            route.status = "superseded"
            route.proof_hash = ""
            route.metadata["activation_status"] = "archived"
            route.metadata["partial_route_fulfilled_by_verified_fact"] = True
            route.metadata["fulfilled_dependency_node_ids"] = sorted(
                node.node_id for node in dependencies if node is not None
            )
            route.metadata["fulfilled_verified_fact_ids"] = sorted(
                verified_fact_ids
            )
            route.metadata["route_retirement_verdict"] = (
                "partial_route_fulfilled"
            )
            route.metadata["route_assembly_contract_last_verdict"] = (
                "partial_route_fulfilled"
            )
            archived.append(route.node_id)
        return archived

    def reconcile_verified_facts(
        self,
        *,
        trigger: str = "",
        ready_before: Optional[Set[str]] = None,
        causal_helper_name: str = "",
        projected_node_ids: Optional[Sequence[str]] = None,
    ) -> Dict[str, Any]:
        """Retire every graph target certified by an accepted visible fact.

        This is deliberately safe to call at every graph/session boundary.
        It handles both orderings: a fact accepted after a target exists and a
        target projected after the fact was already accepted.
        """

        self._rebuild_semantic_fact_registry()
        graph = self.proof_graph
        if graph is None:
            return {
                "resolved_node_ids": [],
                "newly_ready_route_ids": [],
                "fulfilled_partial_route_ids": [],
                "restored_partial_route_ids": [],
                "retracted_proof_idea_ids": [],
            }
        restored_partial_route_ids = self._restore_stale_fact_archives()
        retracted_proof_idea_ids = (
            self._retract_inactive_accepted_fact_lifecycle()
        )
        resolved_all: List[str] = []
        newly_ready_all: List[str] = []
        ready_before_all = (
            set(ready_before)
            if ready_before is not None
            else self._ready_route_ids()
        )
        projected_fact_ids_by_node: Dict[str, str] = {}
        projected_fact_order_by_node: Dict[str, int] = {}
        for helper_order, helper in enumerate(self.verified_helpers.values()):
            if not self._verified_helper_context_visible(helper):
                continue
            helper_environment_hash = str(
                helper.verification_environment_hash or ""
            ).strip()
            current_environment_hash = str(
                self.current_lean_environment_hash or ""
            ).strip()
            if (
                current_environment_hash
                and not self.lean_environment_is_compatible(
                    helper_environment_hash,
                    current_environment_hash,
                )
            ):
                continue
            helper_ready_before = self._ready_route_ids()
            helper_node_id = str(
                graph.helper_name_to_node_id.get(helper.name) or ""
            ).strip()
            helper_node = graph.nodes.get(helper_node_id)
            if helper_node is None or helper_node.status != "proved":
                continue
            helper_statement = helper_decl_statement(helper.source)
            helper_statement_key = canonical_dossier_statement_key(
                helper_statement
            )
            helper_contract_identity = verified_helper_bound_contract_identity(helper)
            fact_id = self._verified_fact_identity(helper)
            if not fact_id:
                continue
            newly_resolved: List[str] = []
            for node in list(graph.nodes.values()):
                if node.kind not in {
                    "proposed_claim",
                    "formal_variant",
                    "missing_obligation",
                    "proof_state_root",
                    "proof_state_child_goal",
                }:
                    continue
                if graph.is_superseded_tombstone(node) or node.status == "proved":
                    continue
                node_environment_hash = str(
                    node.metadata.get(
                        "statement_environment_hash"
                    )
                    or ""
                ).strip()
                if helper_environment_hash != node_environment_hash:
                    continue
                node_statement_key = canonical_dossier_statement_key(node.statement)
                node_contract_identity = self._graph_node_contract_identity(node)
                helper_parsed_identity = parse_lean_contract_identity(
                    helper_contract_identity
                )
                node_parsed_identity = parse_lean_contract_identity(
                    node_contract_identity
                )
                helper_has_structural_identity = helper_parsed_identity is not None
                node_has_structural_identity = node_parsed_identity is not None
                structurally_equal = bool(
                    helper_has_structural_identity
                    and node_has_structural_identity
                    and helper_parsed_identity[0] == node_parsed_identity[0]
                )
                surface_equal = bool(
                    helper_statement_key
                    and node_statement_key
                    and helper_statement_key == node_statement_key
                )
                if (
                    helper_has_structural_identity
                    and node_has_structural_identity
                    and not structurally_equal
                ):
                    # Once both sides carry Lean evidence, the full Expr
                    # identity is authoritative. Surface spelling cannot
                    # override a structural contradiction.
                    continue
                # Legacy/unbound litter: a format-valid Lean token without a
                # matching receipt must still veto surface retirement when it
                # conflicts with the helper's bound identity. Bind strips every
                # alias key, so reinjected litter may use any of them.
                if (
                    helper_has_structural_identity
                    and any(
                        parse_lean_contract_identity(raw) is not None
                        and parse_lean_contract_identity(raw)[0]
                        != helper_parsed_identity[0]
                        for raw in _graph_metadata_raw_lean_identities(
                            dict(getattr(node, "metadata", {}) or {})
                        )
                    )
                    and not structurally_equal
                ):
                    continue
                if not (structurally_equal or surface_equal):
                    continue
                if node.kind == "proposed_claim":
                    graph.mark_claim_proved_by_helper(
                        node.node_id,
                        helper_node_id,
                        source_hash=helper.source_hash,
                        proof_hash=helper.source_hash,
                        support_names=helper.support_names,
                    )
                elif node.kind == "formal_variant":
                    graph.mark_variant_proved_by_helper(
                        node.node_id,
                        helper_node_id,
                        source_hash=helper.source_hash,
                        proof_hash=helper.source_hash,
                        support_names=helper.support_names,
                    )
                elif node.kind == "missing_obligation":
                    graph.mark_obligation_proved_by_helper(
                        node.node_id,
                        helper_node_id,
                        source_hash=helper.source_hash,
                        proof_hash=helper.source_hash,
                        support_names=helper.support_names,
                    )
                else:
                    graph.mark_proof_state_node_proved_by_helper(
                        node.node_id,
                        helper_node_id,
                        source_hash=helper.source_hash,
                        proof_hash=helper.source_hash,
                        support_names=helper.support_names,
                    )
                if node.status == "proved":
                    node.metadata["verified_fact_id"] = fact_id
                    node.metadata["verified_statement_identity"] = fact_id
                    newly_resolved.append(node.node_id)
                    if node.node_id not in resolved_all:
                        resolved_all.append(node.node_id)
            # Registry membership was rebuilt atomically before graph work.
            # This lookup is therefore the current proposition receipt, never
            # an append-only remnant from an older proof attestation.
            receipt = self.semantic_fact_registry[fact_id]
            # Helper projection may have closed matching targets immediately
            # before this idempotent registry pass.  Recover those exact
            # certifications from graph provenance so the durable fact
            # receipt is complete even when ``newly_resolved`` is empty.
            certified_node_ids = list(newly_resolved)
            for node in list(graph.nodes.values()):
                metadata = dict(getattr(node, "metadata", {}) or {})
                if (
                    node.kind
                    in {
                        "proposed_claim",
                        "formal_variant",
                        "missing_obligation",
                        "proof_state_root",
                        "proof_state_child_goal",
                    }
                    and node.status == "proved"
                    and str(
                        metadata.get("verified_by_helper_node_id") or ""
                    ).strip()
                    == helper_node_id
                    and graph._helper_certifies_node(helper_node, node)
                    and node.node_id not in certified_node_ids
                ):
                    certified_node_ids.append(node.node_id)
                if node.node_id in certified_node_ids:
                    node.metadata["verified_fact_id"] = fact_id
                    node.metadata["verified_statement_identity"] = fact_id
            cumulative = receipt.setdefault("resolved_node_ids", [])
            prior_resolved = {
                str(node_id or "").strip()
                for node_id in list(cumulative)
                if str(node_id or "").strip()
            }
            newly_certified_node_ids = [
                node_id
                for node_id in certified_node_ids
                if node_id not in prior_resolved
            ]
            for node_id in newly_certified_node_ids:
                projected_fact_ids_by_node[node_id] = fact_id
                projected_fact_order_by_node[node_id] = helper_order
            for node_id in certified_node_ids:
                if node_id not in cumulative:
                    cumulative.append(node_id)
            receipt["reconciliation_count"] = int(
                receipt.get("reconciliation_count", 0) or 0
            ) + 1
            fact_triggered_routes = set(
                self._ready_route_ids() - helper_ready_before
            )
            fact_triggered_routes = sorted(fact_triggered_routes)
            receipt_routes = receipt.setdefault("newly_ready_route_ids", [])
            for route_id in fact_triggered_routes:
                if route_id not in receipt_routes:
                    receipt_routes.append(route_id)
                if route_id not in newly_ready_all:
                    newly_ready_all.append(route_id)
            if newly_certified_node_ids:
                envelope = ProofLineageEnvelope(
                    statement_identity=fact_id,
                    accepted_fact_id=fact_id,
                )
                self.record_proof_lineage_event(
                    event_type="accepted_fact_retired_targets",
                    envelope=envelope,
                    phase="verified_fact_reconciliation",
                    verdict="targets_retired",
                    evidence_hash=helper.source_hash,
                    details={
                        "trigger": str(trigger or ""),
                        "helper_name": helper.name,
                        "resolved_node_ids": list(newly_certified_node_ids),
                    },
                )
                fact_consumers = self._proof_idea_fact_consumers(
                    newly_certified_node_ids
                )
                for idea_id, consumer in fact_consumers.items():
                    resolved_claims = {
                        claim_id: sorted(node_ids)
                        for claim_id, node_ids in dict(
                            consumer.get("claims") or {}
                        ).items()
                    }
                    idea = self.proof_ideas[idea_id]
                    branch_ids = sorted(consumer.get("branches") or set()) or [""]
                    node_ids = sorted(
                        {
                            node_id
                            for claim_node_ids in resolved_claims.values()
                            for node_id in claim_node_ids
                        }
                    )
                    for branch_id in branch_ids:
                        self.record_proof_idea_observation(
                            idea_id,
                            ProofIdeaObservation.create(
                                proof_idea_id=idea_id,
                                occurrence_key=(
                                    fact_id + ":" + branch_id + ":" + ":".join(node_ids)
                                ),
                                kind="evidence_delta",
                                summary=(
                                    f"accepted fact {fact_id} retired equivalent "
                                    f"graph work: {', '.join(sorted(node_ids))}"
                                ),
                                evidence_hash=helper.source_hash,
                                branch_id=branch_id,
                                turn_index=int(helper.turn_index or 0),
                            ),
                        )
                    idea = self.proof_ideas[idea_id]
                    resolutions = tuple(
                        ProofIdeaClaimResolution.create(
                            proof_idea_id=idea_id,
                            occurrence_key=fact_id,
                            claim_id=claim_id,
                            status="retired",
                            authority="accepted_fact",
                            reason=(
                                "accepted fact retired equivalent graph work"
                            ),
                            evidence_id=fact_id,
                            turn_index=max(0, int(helper.turn_index or 0)),
                            node_ids=tuple(sorted(set(claim_node_ids))),
                        )
                        for claim_id, claim_node_ids in sorted(
                            resolved_claims.items()
                        )
                    )
                    self.upsert_proof_idea(
                        replace(
                            idea,
                            claim_resolutions=idea.claim_resolutions + resolutions,
                        )
                    )
                    idea = self.proof_ideas[idea_id]
                    if idea.claim_intents and all(
                        (
                            resolution := idea.current_claim_resolution(
                                intent.claim_id
                            )
                        )
                        is not None
                        and resolution.status in {"retired", "solved"}
                        for intent in idea.claim_intents
                    ):
                        self.upsert_proof_idea(
                            replace(
                                idea,
                                status_history=idea.status_history
                                + (
                                    ProofIdeaStatusTransition.create(
                                        proof_idea_id=idea_id,
                                        occurrence_key=fact_id,
                                        status="retired",
                                        authority="accepted_fact",
                                        reason=(
                                            "all claim intents were fulfilled by "
                                            "accepted facts"
                                        ),
                                        turn_index=max(
                                            0, int(helper.turn_index or 0)
                                        ),
                                        # Whole-idea retirement may aggregate
                                        # several branch consumers; blank is
                                        # the explicit global scope.
                                        branch_id="",
                                        evidence_id=fact_id,
                                    ),
                                ),
                            )
                        )
        # Consumer topology may grow after a node was first retired (for
        # example, a later route reuses shared graph work). Re-project every
        # live receipt idempotently so those consumers receive lifecycle state
        # even though the graph node itself did not become newly proved.
        converged_fact_ids: Set[str] = set()
        for helper in self.verified_helpers.values():
            if not self._verified_helper_context_visible(helper):
                continue
            fact_id = self._verified_fact_identity(helper)
            receipt = self.semantic_fact_registry.get(fact_id)
            if (
                not fact_id
                or fact_id in converged_fact_ids
                or not isinstance(receipt, dict)
            ):
                continue
            converged_fact_ids.add(fact_id)
            certified_node_ids = [
                str(node_id or "").strip()
                for node_id in list(receipt.get("resolved_node_ids") or [])
                if str(node_id or "").strip()
                and graph._proved_node_has_durable_certificate(
                    graph.nodes.get(str(node_id or "").strip())
                )
            ]
            if certified_node_ids:
                self._ensure_accepted_fact_lifecycle(
                    helper=helper,
                    fact_id=fact_id,
                    node_ids=certified_node_ids,
                )
        fulfilled_partial_route_ids = self._archive_fulfilled_partial_routes()
        ready_after_all = self._ready_route_ids()
        externally_triggered_routes = sorted(
            ready_after_all - ready_before_all
        )
        if projected_fact_ids_by_node:
            for route_id in externally_triggered_routes:
                try:
                    # Receipt attribution only needs dependency ids. The
                    # mutable status path replaces branch frames and would
                    # erase structural fan-in imports on newly-ready routes.
                    route_status = graph.route_assembly_contract_status(
                        route_id,
                        mutate=False,
                    )
                except Exception:
                    continue
                required_ids = {
                    str(node_id or "").strip()
                    for node_id in list(
                        route_status.get("required_node_ids")
                        or route_status.get("dependency_node_ids")
                        or []
                    )
                    if str(node_id or "").strip()
                }
                contributing_nodes = [
                    node_id
                    for node_id in required_ids
                    if node_id in projected_fact_ids_by_node
                ]
                # When graph sync projected several accepted facts before
                # reconciliation sampled readiness, only the final required
                # projection caused an AND-route to cross from incomplete to
                # ready. Preserve the verified-helper insertion order used by
                # sync and attribute exactly that transition, rather than
                # crediting every contributing sibling.
                final_node_id = max(
                    contributing_nodes,
                    key=lambda node_id: projected_fact_order_by_node[node_id],
                    default="",
                )
                final_fact_id = projected_fact_ids_by_node.get(final_node_id, "")
                for fact_id in ([final_fact_id] if final_fact_id else []):
                    receipt = self.semantic_fact_registry.get(fact_id)
                    if not isinstance(receipt, dict):
                        continue
                    receipt_routes = receipt.setdefault(
                        "newly_ready_route_ids",
                        [],
                    )
                    if route_id not in receipt_routes:
                        receipt_routes.append(route_id)
        for route_id in externally_triggered_routes:
            if route_id not in newly_ready_all:
                newly_ready_all.append(route_id)
        if newly_ready_all:
            self.increment_tool_metric(
                "mini_semantic_fact_newly_ready_routes",
                len(newly_ready_all),
            )
        if resolved_all:
            self.increment_tool_metric(
                "mini_semantic_fact_targets_retired",
                len(resolved_all),
            )
        if fulfilled_partial_route_ids:
            self.increment_tool_metric(
                "mini_semantic_fact_partial_routes_fulfilled",
                len(fulfilled_partial_route_ids),
            )
        # Accepted-fact compensation deliberately drops to controller
        # authority. Complete the reduction in the same reconciliation
        # transaction so an already blocked/abandoned/live route immediately
        # replaces the neutral ``active`` compensation instead of waiting for
        # an unrelated later graph event or prompt render.
        self.reconcile_proof_idea_graph_statuses()
        return {
            "resolved_node_ids": resolved_all,
            "newly_ready_route_ids": newly_ready_all,
            "fulfilled_partial_route_ids": fulfilled_partial_route_ids,
            "restored_partial_route_ids": restored_partial_route_ids,
            "retracted_proof_idea_ids": retracted_proof_idea_ids,
        }

    @staticmethod
    def _verified_helper_context_visible(helper: VerifiedHelper) -> bool:
        return str(getattr(helper, "render_policy", "") or "") in {
            "",
            "root_authoritative",
        }

    def is_verified_helper_context_visible(self, helper_or_name: Any) -> bool:
        """Return whether a verified helper is usable/countable proof context."""

        helper = helper_or_name
        if isinstance(helper_or_name, str):
            helper = self.verified_helpers.get(helper_or_name)
        if helper is None:
            return False
        return self._verified_helper_context_visible(helper)

    def visible_accepted_helper_names(
        self,
        helper_names: Iterable[str],
        *,
        include_parent_progress_helpers: bool = False,
    ) -> List[str]:
        """Return accepted helper names allowed to count as reusable progress.

        Verified helpers can be stored for diagnostics, exact negative
        certificates, or route-local assembly without being safe global proof
        context.  Action outcomes expose only context-visible helpers by
        default; hidden graph-certified parent progress is reported through
        parent-progress metadata rather than ``helpers_added``.
        """

        out: List[str] = []
        for raw_name in list(helper_names or ()):
            name = str(raw_name or "").strip()
            if not name or name in out:
                continue
            helper = self.verified_helpers.get(name)
            if helper is None:
                out.append(name)
                continue
            if self._verified_helper_context_visible(helper):
                out.append(name)
                continue
            if include_parent_progress_helpers and strong_progress_for_accepted_helpers(
                self,
                [name],
            ):
                out.append(name)
        return out

    def _answer_safety_kwargs(self) -> Dict[str, bool]:
        return {
            "suppress_solution_placeholders": bool(
                getattr(self, "suppress_solution_placeholders", True)
            ),
            "opaque_mode": bool(getattr(self, "opaque_mode", True)),
            "allow_official_answer_visibility": bool(
                getattr(self, "allow_official_answer_visibility", False)
            ),
            "official_answer_payload_present": getattr(
                self,
                "official_answer_payload_present",
                None,
            ),
        }

    def _verified_helper_answer_safety_metadata(
        self,
        helper: VerifiedHelper,
    ) -> Dict[str, str]:
        """Return a source-bound receipt for the current answer policy."""

        source = str(getattr(helper, "source", "") or "").strip()
        statement = helper_decl_statement(source)
        source_hash = str(getattr(helper, "source_hash", "") or "").strip()
        admission_policy = (
            "official_answer_visible"
            if official_answer_visible_to_llm(
                opaque_mode=bool(getattr(self, "opaque_mode", True)),
                allow_official_answer_visibility=bool(
                    getattr(self, "allow_official_answer_visibility", False)
                ),
                official_answer_payload_present=getattr(
                    self,
                    "official_answer_payload_present",
                    None,
                ),
            )
            else "solution_suppressed"
        )
        metadata = {
            "verified_helper_answer_safety_policy": admission_policy,
        }
        receipt = graph_helper_answer_safety_receipt(
            source_hash=source_hash,
            source_digest=hashlib.sha256(
                source.encode("utf-8", errors="replace")
            ).hexdigest(),
            statement_key=canonical_dossier_statement_key(statement),
            environment_hash=str(
                getattr(helper, "verification_environment_hash", "") or ""
            ).strip(),
            render_policy=str(getattr(helper, "render_policy", "") or "").strip(),
            visibility_policy=str(
                getattr(helper, "visibility_policy", "") or ""
            ).strip(),
            admission_policy=admission_policy,
        )
        if receipt:
            metadata["verified_helper_answer_safety_receipt"] = receipt
        return metadata

    def _visible_verified_support_candidates(
        self,
        *,
        skip_name: str = "",
    ) -> List[Tuple[str, Tuple[str, ...]]]:
        support = _dossier_support_candidates(
            self.root_statement,
            include_implication_premises=True,
            premises_are_assumptions=True,
        )
        for name, helper in self.verified_helpers.items():
            if str(name or "") == str(skip_name or ""):
                continue
            if not self._verified_helper_context_visible(helper):
                continue
            statement = helper_decl_statement(helper.source)
            if statement:
                support.extend(_dossier_support_candidates(statement))
        return support

    def activate_active_root_classification_preamble(self, preamble: str) -> None:
        self.active_root_classification_preamble_hash = (
            text_hash(preamble) if str(preamble or "").strip() else ""
        )

    def active_root_equivalence_statements_for_current_frame(
        self,
        *,
        helper_blocks: Optional[Sequence[str]] = None,
        require_helper_context_hash_match: bool = True,
    ) -> Tuple[str, ...]:
        return active_root_equivalence_statements(
            self.active_root_targets_for_current_frame(
                helper_blocks=helper_blocks,
                require_helper_context_hash_match=require_helper_context_hash_match,
            )
        )

    def active_root_targets_for_current_frame(
        self,
        *,
        helper_blocks: Optional[Sequence[str]] = None,
        require_helper_context_hash_match: bool = True,
    ) -> Tuple[Dict[str, Any], ...]:
        root_key = canonical_dossier_statement_key(self.root_statement)
        current_preamble_hash = str(
            getattr(self, "active_root_classification_preamble_hash", "") or ""
        ).strip()
        if not root_key or not current_preamble_hash:
            return ()
        if helper_blocks is None:
            try:
                helper_blocks = self.verified_helper_blocks()
            except Exception:
                helper_blocks = [
                    str(item.source or "").strip()
                    for item in self.verified_helpers.values()
                    if self._verified_helper_context_visible(item)
                    and str(getattr(item, "source", "") or "").strip()
                ]
        helper_key = text_hash(
            "\n".join(
                sorted(
                    str(block or "").strip()
                    for block in list(helper_blocks or ())
                    if str(block or "").strip()
                )
            )
        )
        framed: List[Dict[str, Any]] = []
        for raw in list(getattr(self, "active_root_targets", []) or ()):
            if not isinstance(raw, dict):
                continue
            item_root_key = str(raw.get("root_statement_key") or "").strip()
            item_preamble_hash = str(raw.get("preamble_hash") or "").strip()
            item_helper_hash = str(raw.get("helper_context_hash") or "").strip()
            if item_root_key != root_key or item_preamble_hash != current_preamble_hash:
                continue
            if require_helper_context_hash_match and item_helper_hash != helper_key:
                continue
            framed.append(dict(raw))
        return tuple(framed)

    def _active_root_targets_for_verified_helper_context(
        self,
        helper: VerifiedHelper,
    ) -> List[Dict[str, Any]]:
        root_key = canonical_dossier_statement_key(self.root_statement)
        if not root_key:
            return []
        current_preamble_hash = str(
            getattr(self, "active_root_classification_preamble_hash", "") or ""
        ).strip()
        if not current_preamble_hash:
            return []
        helper_blocks = [
            str(item.source or "").strip()
            for name, item in self.verified_helpers.items()
            if str(name or "").strip() != str(helper.name or "").strip()
            and self._verified_helper_context_visible(item)
            and str(getattr(item, "source", "") or "").strip()
        ]
        helper_key = text_hash("\n".join(sorted(helper_blocks)))
        framed: List[Dict[str, Any]] = []
        for raw in list(getattr(self, "active_root_targets", []) or ()):
            if not isinstance(raw, dict):
                continue
            item_root_key = str(raw.get("root_statement_key") or "").strip()
            item_preamble_hash = str(raw.get("preamble_hash") or "").strip()
            item_helper_hash = str(raw.get("helper_context_hash") or "").strip()
            if (
                item_root_key == root_key
                and item_preamble_hash == current_preamble_hash
                and item_helper_hash == helper_key
            ):
                framed.append(dict(raw))
        return framed

    def _classify_verified_helper_quality(self, helper: VerifiedHelper) -> None:
        statement = helper_decl_statement(helper.source)
        admission_quality = verified_helper_admission_quality(helper)
        premises, conclusion, bound_names = _dossier_statement_premises_and_conclusion(
            statement
        )
        has_lean_contract_evidence = bool(
            has_lean_contract_identity(
                str(getattr(helper, "contract_identity", "") or "")
            )
        )
        if has_lean_contract_evidence:
            premises = tuple(
                str(item or "")
                for item in (
                    getattr(helper, "contract_proof_binder_types", []) or []
                )
                if str(item or "").strip()
            )
        tags: List[str] = []
        open_keys: List[str] = []
        open_statements: List[str] = []
        closed_open_statements: List[str] = []
        closed_premises = list(graph_statement_closed_premises(statement))
        data_requirements = list(
            graph_statement_closed_data_requirements(
                statement,
                reference_statement=self.root_statement,
            )
        )
        ambiguous_binder_types = (
            []
            if has_lean_contract_evidence
            else list(graph_statement_contract_ambiguities(statement))
        )
        render_policy = ""
        provenance_tags = [
            str(tag or "").strip()
            for tag in list(getattr(helper, "provenance_tags", []) or [])
            if str(tag or "").strip()
        ]
        visibility_policy = str(
            getattr(helper, "visibility_policy", "") or ""
        ).strip()
        active_target_statements = active_root_equivalence_statements(
            self._active_root_targets_for_verified_helper_context(helper)
        )
        phase_text = str(getattr(helper, "phase", "") or "").strip().lower()
        placeholder_root_equivalence_allowed = (
            dossier_root_equivalence_placeholder(self.root_statement)
            and "subpass" in phase_text
        )
        root_equivalence_root_statement = (
            str(self.root_statement or "").strip()
            if (
                not dossier_root_equivalence_placeholder(self.root_statement)
                or placeholder_root_equivalence_allowed
            )
            else ""
        )
        root_equivalence_active_targets = tuple(active_target_statements)
        statement_key = canonical_dossier_statement_key(statement)
        root_candidate_keys = {
            key
            for key in [
                canonical_dossier_statement_key(root_equivalence_root_statement),
                *(
                    canonical_dossier_statement_key(target)
                    for target in root_equivalence_active_targets
                ),
            ]
            if key
        }
        root_equivalent = bool(statement_key and statement_key in root_candidate_keys)
        root_equivalence_reference = root_equivalence_root_statement
        active_equivalence_targets = root_equivalence_active_targets
        if not root_equivalence_reference and root_equivalence_active_targets:
            root_equivalence_reference = root_equivalence_active_targets[0]
            active_equivalence_targets = root_equivalence_active_targets[1:]
        if not root_equivalent and statement and root_equivalence_reference:
            root_equivalent = _dossier_statement_root_equivalent(
                statement,
                root_equivalence_reference,
                active_target_statements=active_equivalence_targets,
            )
        root_authoritative = bool(
            visibility_policy == "root_authoritative"
            or any(
                tag
                in {
                    "root_authoritative_helper",
                    "root_exact_certificate",
                    "root_finalization_certificate",
                }
                for tag in provenance_tags
            )
        )
        root_adjacent = _dossier_statements_root_adjacent(
            conclusion,
            self.root_statement,
            conclusion_bound_names=bound_names,
        )
        root_has_negative_conclusion = _dossier_statement_has_negative_conclusion(
            self.root_statement
        )
        # A premise projection is still a valid, context-visible Lean theorem:
        # callers may use it to name or transport an assumption.  It is not,
        # however, new mathematical evidence.  Tag it without hiding it so
        # progress accounting and cache publication can enforce that separate
        # policy while ordinary replay remains available.
        if graph_statement_has_circular_premise(statement):
            tags.append("premise_projection_helper")
        if not admission_quality.generic_novelty:
            tags.append("structurally_vacuous_helper")
            tags.append(
                f"helper_quality:{admission_quality.classification}"
            )
        if root_equivalent:
            tags.append("root_equivalent_helper")
            if not root_authoritative:
                render_policy = "advisory_root_equivalent"
        if ambiguous_binder_types:
            tags.extend(
                ["unresolved_binder_contract", "requires_unproved_premise"]
            )
            for ambiguous_type in ambiguous_binder_types:
                key = canonical_dossier_statement_key(ambiguous_type)
                if key and key not in open_keys:
                    open_keys.append(key)
                    open_statements.append(ambiguous_type)
                    closed_open_statements.append(ambiguous_type)
            if not root_authoritative:
                render_policy = "advisory_requires_unproved_premise"
        if (premises or data_requirements) and _dossier_statements_root_adjacent(
            conclusion,
            self.root_statement,
            conclusion_bound_names=bound_names,
        ):
            support = self._visible_verified_support_candidates(
                skip_name=helper.name,
            )
            for requirement in data_requirements:
                requirement_text, requirement_names = (
                    _dossier_strip_leading_forall_binders_with_names(requirement)
                )
                requirement_bound_names = tuple(
                    dict.fromkeys(bound_names + requirement_names)
                )
                if _dossier_support_contains(
                    requirement_text,
                    support,
                    premise_bound_names=requirement_bound_names,
                ):
                    continue
                key = canonical_dossier_statement_key(requirement_text)
                if key and key not in open_keys:
                    open_keys.append(key)
                    open_statements.append(requirement_text)
                    closed_open_statements.append(requirement)
            for premise_index, premise in enumerate(premises):
                premise_text, premise_names = (
                    _dossier_strip_leading_forall_binders_with_names(premise)
                )
                if not premise_text:
                    continue
                premise_bound_names = tuple(dict.fromkeys(bound_names + premise_names))
                if _dossier_support_contains(
                    premise_text,
                    support,
                    premise_bound_names=premise_bound_names,
                ):
                    continue
                key = canonical_dossier_statement_key(premise_text)
                if key and key not in open_keys:
                    open_keys.append(key)
                    open_statements.append(premise_text)
                    if premise_index < len(closed_premises):
                        closed_open_statements.append(closed_premises[premise_index])
            if open_keys:
                tags.append("hollow_root_reducer")
                tags.append("requires_unproved_premise")
                if not render_policy and not root_authoritative:
                    render_policy = "advisory_requires_unproved_premise"
        if root_authoritative:
            # This policy is granted only by an authoritative root receipt
            # (for example a fresh Lean replay proving the selected parent
            # contract).  Its theorem binders are the root's local context,
            # not global obligations that should hide the checked theorem.
            render_policy = "root_authoritative"
        if (
            not render_policy
            and not root_adjacent
            and not root_has_negative_conclusion
            and (
                _dossier_statement_is_negative_evidence(conclusion)
                or _dossier_statement_is_existential_counterexample(
                    statement,
                    self.root_statement,
                )
            )
        ):
            tags.append("negative_evidence_helper")
            render_policy = "advisory_negative_evidence"
        if not render_policy and visibility_policy:
            render_policy = visibility_policy
        for tag in provenance_tags:
            if tag not in tags:
                tags.append(tag)

        helper.quality_tags = tags
        helper.open_premise_statement_keys = open_keys
        helper.open_premise_statements = open_statements
        helper.closed_open_premise_statements = closed_open_statements
        helper.render_policy = render_policy

    def _refresh_verified_helper_quality(self) -> None:
        for helper in list(self.verified_helpers.values()):
            old_policy = str(getattr(helper, "render_policy", "") or "")
            self._classify_verified_helper_quality(helper)
            if not verified_helper_admission_quality(helper).generic_novelty:
                stale_delta = _coerce_verified_helper_progress_delta(
                    self.verified_helper_progress_deltas.get(helper.name)
                )
                if stale_delta is not None:
                    stale_delta.theory_progress = False
                    stale_delta.resolved_claim_node_ids.clear()
                    stale_delta.resolved_variant_node_ids.clear()
                    stale_delta.resolved_obligation_node_ids.clear()
                    self.verified_helper_progress_deltas[helper.name] = stale_delta
            if self.proof_graph is not None:
                node_id = self.proof_graph.helper_name_to_node_id.get(helper.name, "")
                node = self.proof_graph.nodes.get(node_id) if node_id else None
                if node is not None:
                    node.metadata["verified_helper_provenance_tags"] = list(
                        getattr(helper, "provenance_tags", []) or []
                    )
                    node.metadata["verified_helper_visibility_policy"] = str(
                        getattr(helper, "visibility_policy", "") or ""
                    )
                    node.metadata["verified_helper_quality_tags"] = list(
                        helper.quality_tags
                    )
                    node.metadata["verified_helper_render_policy"] = helper.render_policy
                    node.metadata.update(
                        self._verified_helper_answer_safety_metadata(helper)
                    )
                    node.metadata["verified_helper_open_premise_statement_keys"] = list(
                        helper.open_premise_statement_keys
                    )
                    node.metadata["verified_helper_open_premise_statements"] = list(
                        helper.closed_open_premise_statements
                    )
            if (
                old_policy
                and not helper.render_policy
                and verified_helper_admission_quality(helper).generic_novelty
            ):
                self.increment_tool_metric(
                    "mini_hollow_root_reducers_reenabled_by_premise",
                    1,
                )
                if self.proof_graph is not None:
                    statement_key = canonical_dossier_statement_key(
                        helper_decl_statement(helper.source)
                    )
                    node_id = self.proof_graph.helper_name_to_node_id.get(
                        helper.name,
                        "",
                    )
                    if statement_key and node_id:
                        resolved_claim_node_ids: List[str] = []
                        resolved_variant_node_ids: List[str] = []
                        resolved_obligation_node_ids: List[str] = []
                        _supersede_graph_native_proposals_for_helper_name(
                            self,
                            helper.name,
                            verified_statement_key=statement_key,
                            verified_node_id=node_id,
                        )
                        _resolve_graph_native_claims_for_statement_key(
                            self,
                            statement_key=statement_key,
                            verified_helper_name=helper.name,
                            verified_node_id=node_id,
                            source_hash=helper.source_hash,
                            proof_hash=helper.source_hash,
                            support_names=list(helper.support_names),
                            resolved_claim_node_ids=resolved_claim_node_ids,
                            resolved_variant_node_ids=resolved_variant_node_ids,
                        )
                        _resolve_graph_native_obligations_for_statement_key(
                            self,
                            statement_key=statement_key,
                            verified_helper_name=helper.name,
                            verified_node_id=node_id,
                            source_hash=helper.source_hash,
                            proof_hash=helper.source_hash,
                            support_names=list(helper.support_names),
                            resolved_obligation_node_ids=resolved_obligation_node_ids,
                        )
                        _merge_verified_helper_progress_delta(
                            self,
                            helper,
                            statement_key=statement_key,
                            resolved_claim_node_ids=resolved_claim_node_ids,
                            resolved_variant_node_ids=resolved_variant_node_ids,
                            resolved_obligation_node_ids=resolved_obligation_node_ids,
                        )

    def _refresh_verified_helper_statement_aliases(
        self,
        *,
        record_metric: bool = False,
    ) -> None:
        live_helpers = dict(getattr(self, "verified_helpers", {}) or {})
        valid_aliases: Dict[str, str] = {}
        canonical_by_fact_key: Dict[Tuple[str, str, str], str] = {}

        def helper_fact_key(name: str) -> Tuple[str, str, str]:
            helper = live_helpers.get(name)
            if helper is None or not self._verified_helper_context_visible(helper):
                return ("", "", "")
            statement_key = canonical_dossier_statement_key(
                helper_decl_statement(helper.source)
            )
            # Include unresolved support names with a stable missing sentinel so
            # two same-statement helpers that depend on different absent
            # supports are not collapsed into one alias key.
            support_hashes = dict(helper.support_source_hashes or {})
            dependency_pairs: List[Tuple[str, str]] = []
            seen_deps: set[str] = set()
            for raw_dep in list(helper.support_names or []):
                dep_name = str(raw_dep or "").strip()
                if not dep_name or dep_name in seen_deps:
                    continue
                seen_deps.add(dep_name)
                source_hash = str(support_hashes.get(dep_name) or "").strip()
                dependency_pairs.append(
                    (dep_name, source_hash or f"missing:{dep_name}")
                )
            for raw_dep, raw_hash in support_hashes.items():
                dep_name = str(raw_dep or "").strip()
                source_hash = str(raw_hash or "").strip()
                if not dep_name or dep_name in seen_deps or not source_hash:
                    continue
                seen_deps.add(dep_name)
                dependency_pairs.append((dep_name, source_hash))
            dependency_hashes = json.dumps(
                sorted(dependency_pairs),
                separators=(",", ":"),
            )
            return (
                statement_key,
                str(helper.verification_environment_hash or "").strip(),
                dependency_hashes,
            )

        for raw_req, raw_canonical in list(
            (getattr(self, "verified_helper_statement_aliases", {}) or {}).items()
        ):
            req = str(raw_req or "").strip()
            canonical = str(raw_canonical or "").strip()
            if not req or not canonical or req not in live_helpers or canonical not in live_helpers:
                continue
            req_key = helper_fact_key(req)
            canonical_key = helper_fact_key(canonical)
            if req_key[0] and req_key == canonical_key:
                valid_aliases[req] = canonical
                canonical_by_fact_key.setdefault(req_key, canonical)

        for name, helper in live_helpers.items():
            if name in valid_aliases or not self._verified_helper_context_visible(helper):
                continue
            fact_key = helper_fact_key(name)
            if not fact_key[0]:
                continue
            canonical = canonical_by_fact_key.setdefault(fact_key, name)
            if canonical != name:
                valid_aliases[name] = canonical

        newly_recorded = [
            name
            for name, canonical in valid_aliases.items()
            if self.verified_helper_statement_aliases.get(name) != canonical
        ]
        self.verified_helper_statement_aliases = valid_aliases
        if newly_recorded and record_metric:
            self.increment_tool_metric(
                "mini_verified_helper_statement_aliases_recorded",
                len(newly_recorded),
            )
        self._refresh_verified_helper_progress_alias_fields()

    def _refresh_verified_helper_progress_alias_fields(self) -> None:
        for name, delta in list(self.verified_helper_progress_deltas.items()):
            helper = self.verified_helpers.get(name)
            if helper is None:
                self.verified_helper_progress_deltas.pop(name, None)
                continue
            canonical_helper_name = self.verified_helper_statement_aliases.get(
                name, name
            )
            delta.canonical_helper_name = canonical_helper_name
            delta.theory_progress = bool(
                canonical_helper_name == name
                and _verified_helper_counts_for_theory_progress(self, helper)
            )

    def record_active_root_targets(self, targets: Iterable[Dict[str, Any]]) -> None:
        """Persist Lean-derived root goals after answer-placeholder simplification."""

        cleaned: List[Dict[str, Any]] = []
        seen: Set[str] = set()
        for item in list(targets or ()):
            if not isinstance(item, dict):
                continue
            raw_target = " ".join(str(item.get("target") or "").split()).strip()
            working_target = " ".join(
                str(item.get("working_target") or "").split()
            ).strip()
            target = working_target or raw_target
            if not target:
                continue
            hypotheses = [
                " ".join(str(hyp or "").split()).strip()
                for hyp in list(item.get("hypotheses") or ())
                if str(hyp or "").strip()
            ]
            record: Dict[str, Any] = {
                "target": target,
                "hypotheses": hypotheses,
            }
            if working_target and raw_target and raw_target != target:
                record["kernel_target"] = raw_target
            for key in (
                "kernel_target",
                "target_source",
                "validation",
                "root_statement_key",
                "preamble_hash",
                "helper_context_hash",
                "official_answer_visible",
            ):
                value = " ".join(str(item.get(key) or "").split()).strip()
                if value:
                    record[key] = value
            closed_targets = active_root_equivalence_statements([record])
            closed_target_key = (
                graph_statement_key(closed_targets[0])
                if len(closed_targets) == 1
                else ""
            )
            # Two proof states may have the same displayed target while their
            # local telescopes differ.  Bare-target dedup silently discarded
            # one such root obligation; deduplicate the closed proposition.
            dedup_key = closed_target_key or graph_statement_key(target)
            if dedup_key in seen:
                continue
            seen.add(dedup_key)
            # Lean-derived structural identity is useful only while it remains
            # bound to this exact closed active target and environment.  Keep
            # the evidence quartet atomically; copying individual fields would
            # let normalization or checkpoint restore manufacture authority.
            identity = str(item.get("contract_identity") or "").strip()
            statement_key = str(
                item.get("contract_identity_statement_key") or ""
            ).strip()
            environment_hash = str(
                item.get("contract_identity_environment_hash") or ""
            ).strip()
            evidence_receipt = str(
                item.get("contract_identity_evidence_receipt") or ""
            ).strip()
            closed_statement_key = (
                closed_target_key
            )
            if (
                identity
                and statement_key
                and statement_key == closed_statement_key
                and lean_contract_evidence_receipt_matches(
                    evidence_receipt,
                    identity=identity,
                    statement_key=statement_key,
                    environment_hash=environment_hash,
                )
            ):
                record.update(
                    {
                        "contract_identity": identity,
                        "contract_identity_statement_key": statement_key,
                        "contract_identity_environment_hash": environment_hash,
                        "contract_identity_evidence_receipt": evidence_receipt,
                    }
                )
            cleaned.append(record)
        self.active_root_targets = cleaned
        if self.proof_graph is not None:
            setter = getattr(self.proof_graph, "set_active_root_target_statements", None)
            if callable(setter):
                setter(active_root_equivalence_statements(cleaned))
            identity_setter = getattr(
                self.proof_graph,
                "set_active_root_target_contract_identities",
                None,
            )
            if callable(identity_setter):
                identity_setter(
                    str(item.get("contract_identity") or "").strip()
                    for item in cleaned
                    if str(item.get("contract_identity") or "").strip()
                )

    def render_active_root_target_context(
        self,
        *,
        max_targets: int = 3,
        active_root_targets: Optional[Sequence[Dict[str, Any]]] = None,
    ) -> str:
        raw_targets = (
            list(active_root_targets or ())
            if active_root_targets is not None
            else list(getattr(self, "active_root_targets", []) or ())
        )
        targets = [
            dict(item)
            for item in raw_targets
            if isinstance(item, dict) and str(item.get("target") or "").strip()
        ][: max(1, int(max_targets or 1))]
        if not targets:
            return ""
        lines = [
            "Lean-derived active root target (authoritative working target):",
            (
                "- The verifier has mechanically discharged the `_solution` "
                "answer shell for this prompt. The remaining mathematical "
                "goal(s) below are the authoritative target(s) for this turn."
            ),
        ]
        for index, item in enumerate(targets, start=1):
            hypotheses = [
                _prompt_safe_inline_text(str(hyp or ""), limit=180)
                for hyp in list(item.get("hypotheses") or [])[:6]
                if str(hyp or "").strip()
            ]
            if hypotheses:
                lines.append(
                    "- Submit a complete Lean proof that introduces the "
                    "active goal's local hypotheses and closes its target "
                    "inside the theorem. A standalone proof of only the "
                    "target line is not a complete top-level proof. Do not "
                    "reason from the `_solution` value (do not reason from "
                    "that value), and do not prove by vacuity."
                )
            else:
                lines.append(
                    "- Submit a proof of the active goal directly. Do not "
                    "re-prove the `↔ _solution` shell, refute the active "
                    "goal, reason from the `_solution` value (do not reason "
                    "from that value), or prove by vacuity."
                )
            if hypotheses:
                lines.append(f"- active goal {index} hypotheses: " + "; ".join(hypotheses))
            target = _prompt_safe_inline_text(str(item.get("target") or ""), limit=700)
            if target:
                lines.append(f"- active goal {index} target: `{target}`")
        return "\n".join(lines)

    def reset_proof_graph(self) -> None:
        self.proof_graph = ProofGraph(
            theorem_name=self.theorem_name,
            root_statement=self.root_statement,
        )
        if self.active_root_targets:
            self.record_active_root_targets(self.active_root_targets)
        ready_before = self._ready_route_ids()
        self._sync_legacy_helpers_to_graph()
        self._sync_proposed_helpers_to_graph()
        self.reconcile_verified_facts(
            trigger="proof_graph_reset",
            ready_before=ready_before,
        )

    def _sync_legacy_helpers_to_graph(self) -> None:
        if self.proof_graph is None:
            return
        answer_safety_kwargs = self._answer_safety_kwargs()
        safe_helpers: Dict[str, VerifiedHelper] = {}
        removed_names: set[str] = set()
        for name, helper in self.verified_helpers.items():
            declared = helper_decl_name(helper.source)
            statement = helper_decl_statement(helper.source)
            if (
                not helper.source
                or not statement
                or graph_statement_non_theorem_reason(statement)
                or is_answer_unsafe_helper_source(
                    helper.source,
                    **answer_safety_kwargs,
                )
                or declared != helper.name
            ):
                removed_names.update(
                    item
                    for item in (str(name or ""), str(helper.name or ""))
                    if item
                )
                continue
            safe_helpers[name] = helper
        for node in list(self.proof_graph.nodes.values()):
            if node.kind != "helper":
                continue
            if str(node.name or "").strip() not in safe_helpers:
                removed_names.add(node.name)
                continue
            probe = f"lemma {node.name} : True := by\n  trivial"
            if is_answer_unsafe_helper_source(probe, **answer_safety_kwargs):
                removed_names.add(node.name)
        for name in removed_names:
            self.proof_graph.remove_helper(name)
        removed_by_sync = max(
            0, len(self.verified_helpers) - len(safe_helpers)
        )
        if removed_by_sync:
            # This path drops helpers wholesale (answer-unsafe, non-theorem,
            # name mismatch) without going through remove_verified_helper, so
            # the generation has to be advanced here too or the durable state
            # silently moves backwards onto an already-seen signature.
            self.verified_helper_eviction_generation += removed_by_sync
        self.verified_helpers = safe_helpers
        # Fix 1 follow-up (2026-05-22): drop alias entries that point at
        # filtered-out helpers, or whose own key was filtered out.
        # Without this, ``resolve_verified_helper_name`` could return a
        # name no longer in verified_helpers.
        live_names = set(safe_helpers.keys())
        self.verified_helper_statement_aliases = {
            req: canonical
            for req, canonical in self.verified_helper_statement_aliases.items()
            if req in live_names and canonical in live_names
        }
        self.verified_helper_progress_deltas = {
            name: delta
            for name, delta in self.verified_helper_progress_deltas.items()
            if name in live_names
        }
        self._refresh_verified_helper_quality()
        self._refresh_verified_helper_statement_aliases()
        self.verified_helper_progress_deltas = {}
        for helper in self.verified_helpers.values():
            statement = helper_decl_statement(helper.source)
            statement_key = canonical_dossier_statement_key(statement)
            resolved_claim_node_ids: List[str] = []
            resolved_variant_node_ids: List[str] = []
            resolved_obligation_node_ids: List[str] = []
            node = self.proof_graph.ensure_helper(
                helper.name,
                statement=statement,
                phase=helper.phase,
                turn_index=helper.turn_index,
                support_names=list(helper.support_names),
                metadata={
                    "verified_helper_source": helper.source,
                    "verified_helper_source_hash": helper.source_hash,
                    **self._verified_helper_answer_safety_metadata(helper),
                    "verified_helper_visibility_policy": helper.visibility_policy,
                    "verified_helper_quality_tags": list(helper.quality_tags),
                    "verified_helper_render_policy": helper.render_policy,
                    "verified_helper_open_premise_statement_keys": list(
                        helper.open_premise_statement_keys
                    ),
                    "verified_helper_open_premise_statements": list(
                        helper.closed_open_premise_statements
                    ),
                    "verified_helper_contract_identity": (
                        verified_helper_bound_contract_identity(helper)
                    ),
                    "verified_helper_contract_identity_statement_key": str(
                        helper.contract_identity_statement_key or ""
                    ),
                    "verified_helper_contract_identity_environment_hash": str(
                        helper.contract_identity_environment_hash or ""
                    ),
                    "verified_helper_contract_identity_evidence_receipt": str(
                        helper.contract_identity_evidence_receipt or ""
                    ),
                    "verified_helper_contract_display_statement": (
                        helper.contract_display_statement
                    ),
                    "verified_helper_contract_binder_sorts": list(
                        helper.contract_binder_sorts
                    ),
                    "verified_helper_contract_proof_binder_types": list(
                        helper.contract_proof_binder_types
                    ),
                    "verified_helper_environment_hash": str(
                        helper.verification_environment_hash or ""
                    ),
                },
            )
            reviver = getattr(self.proof_graph, "revive_verified_helper_node", None)
            if callable(reviver):
                try:
                    reviver(node.node_id)
                except Exception:
                    pass
            self.proof_graph.mark_node_proved(
                node.node_id,
                source_hash=helper.source_hash,
                proof_hash=helper.source_hash,
                support_names=list(helper.support_names),
            )
            proved_node = self.proof_graph.nodes.get(node.node_id)
            if (
                proved_node is None
                or str(getattr(proved_node, "status", "") or "") != "proved"
                or str(getattr(proved_node, "source_hash", "") or "").strip()
                != str(helper.source_hash or "").strip()
            ):
                self.increment_tool_metric(
                    "mini_verified_helper_graph_certification_failed",
                    1,
                )
            if self._verified_helper_context_visible(helper):
                if verified_helper_admission_quality(helper).generic_novelty:
                    _supersede_graph_native_proposals_for_helper_name(
                        self,
                        helper.name,
                        verified_statement_key=statement_key,
                        verified_node_id=node.node_id,
                    )
                _resolve_graph_native_claims_for_statement_key(
                    self,
                    statement_key=statement_key,
                    verified_helper_name=helper.name,
                    verified_node_id=node.node_id,
                    source_hash=helper.source_hash,
                    proof_hash=helper.source_hash,
                    support_names=list(helper.support_names),
                    resolved_claim_node_ids=resolved_claim_node_ids,
                    resolved_variant_node_ids=resolved_variant_node_ids,
                )
            elif str(getattr(helper, "render_policy", "") or "").strip() == (
                "advisory_negative_evidence"
            ):
                _resolve_graph_native_claims_for_statement_key(
                    self,
                    statement_key=statement_key,
                    verified_helper_name=helper.name,
                    verified_node_id=node.node_id,
                    source_hash=helper.source_hash,
                    proof_hash=helper.source_hash,
                    support_names=list(helper.support_names),
                    resolved_claim_node_ids=resolved_claim_node_ids,
                    resolved_variant_node_ids=resolved_variant_node_ids,
                )
                _resolve_graph_native_obligations_for_statement_key(
                    self,
                    statement_key=statement_key,
                    verified_helper_name=helper.name,
                    verified_node_id=node.node_id,
                    source_hash=helper.source_hash,
                    proof_hash=helper.source_hash,
                    support_names=list(helper.support_names),
                    resolved_obligation_node_ids=resolved_obligation_node_ids,
                )
            canonical_helper_name = self.verified_helper_statement_aliases.get(
                helper.name, helper.name
            )
            self.verified_helper_progress_deltas[helper.name] = (
                VerifiedHelperProgressDelta(
                    helper_name=helper.name,
                    statement_key=statement_key,
                    canonical_helper_name=canonical_helper_name,
                    theory_progress=bool(
                        canonical_helper_name == helper.name
                        and _verified_helper_counts_for_theory_progress(self, helper)
                    ),
                    resolved_claim_node_ids=(
                        list(resolved_claim_node_ids)
                        if verified_helper_admission_quality(helper).generic_novelty
                        else []
                    ),
                    resolved_variant_node_ids=(
                        list(resolved_variant_node_ids)
                        if verified_helper_admission_quality(helper).generic_novelty
                        else []
                    ),
                    resolved_obligation_node_ids=(
                        list(resolved_obligation_node_ids)
                        if verified_helper_admission_quality(helper).generic_novelty
                        else []
                    ),
                )
            )
        _resolve_graph_native_obligations_against_verified_helpers(self)
        if removed_by_sync:
            # Unsafe-helper filtering is an authoritative removal path that
            # bypasses remove_verified_helper. Publish its fact view in one
            # assignment so no removed attestation remains observable. A
            # no-op graph sync deliberately leaves copied cumulative receipts
            # intact; ordinary add/upgrade/remove paths reconcile separately.
            self._rebuild_semantic_fact_registry()

    def _sync_proposed_helpers_to_graph(self) -> None:
        if self.proof_graph is None:
            return
        for item in list(self.proposed_helpers.values()):
            self.record_proposed_helper(
                item.source,
                phase=item.phase,
                turn_index=item.turn_index,
            )

    def verified_helper_blocks(
        self,
        *,
        refresh_quality: bool = True,
    ) -> List[str]:
        """Render verified helpers, optionally from the current frozen state.

        Quality refresh is a reconciliation operation: it can update graph
        nodes, resolve obligations, and emit metrics. Scheduler quotation must
        therefore explicitly request the non-refreshing view.
        """

        if refresh_quality:
            self._refresh_verified_helper_quality()
        answer_safety_kwargs = self._answer_safety_kwargs()
        helpers = list(self.verified_helpers.items())
        if not helpers:
            return []
        visible_names = {
            str(name or "")
            for name, item in helpers
            if str(name or "") and self._verified_helper_context_visible(item)
        }
        by_name = {
            str(name or ""): item
            for name, item in helpers
            if str(name or "") and str(name or "") in visible_names
        }
        renderable_names = self._verified_helper_renderable_names(by_name)
        emitted: Set[str] = set()
        ordered: List[VerifiedHelper] = []
        pending = [
            (name, item)
            for name, item in helpers
            if str(name or "") in by_name and str(name or "") in renderable_names
        ]
        while pending:
            progressed = False
            next_pending: List[Tuple[str, VerifiedHelper]] = []
            for name, item in pending:
                support_names = [
                    str(support or "").strip()
                    for support in (
                        list(getattr(item, "support_names", []) or [])
                        + list(getattr(item, "replay_context_names", []) or [])
                    )
                    if str(support or "").strip()
                    and str(support or "").strip() != str(name or "")
                    and str(support or "").strip() in by_name
                ]
                if all(support in emitted for support in support_names):
                    ordered.append(item)
                    emitted.add(str(name or ""))
                    progressed = True
                else:
                    next_pending.append((name, item))
            if not progressed:
                ordered.extend(item for _name, item in next_pending)
                break
            pending = next_pending
        # Variant-collapse: proved variants of the SAME statement accumulate as
        # separate helpers (observed: 40 helpers / 9 distinct statements, one
        # lemma proved 14x across passes). Every one is re-elaborated in full on
        # every Lean scratch/verify check. Emit the second+ occurrence of an
        # EXACT (whitespace-normalized) folded statement as a trivial alias
        # `theorem DUP : STMT := CANONICAL` instead of its full proof: this keeps
        # every name in scope (citation-safe) but collapses the redundant proof
        # work. Gated on exact-statement equality (guarantees the alias
        # typechecks — same type, canonical already proves it) and processed in
        # the topologically-ordered list so a canonical is always emitted before
        # its aliases. Universe-polymorphic headers are left untouched (the name
        # cannot be reconstructed without the `.{u}` params).
        result: List[str] = []
        canonical_name_by_statement: Dict[str, str] = {}
        for item in ordered:
            source = str(item.source or "")
            if is_answer_unsafe_helper_source(source, **answer_safety_kwargs):
                continue
            statement = helper_decl_statement(source)
            if is_answer_unsafe_statement_text(statement, **answer_safety_kwargs):
                continue
            if not self._verified_helper_context_visible(item):
                continue
            name = helper_decl_name(source)
            statement_norm = " ".join(str(statement or "").split())
            header = source.split(":=", 1)[0]
            # Only collapse SUBSTANTIVE duplicate statements: trivial/generic
            # props (`True`, `False`, tiny equalities) are cheap to re-elaborate
            # and are shared incidentally by role-distinct placeholder helpers, so
            # aliasing them yields no compute benefit and would conflate them.
            # 16 matches the dependency-contract "too short to be meaningful"
            # threshold. Universe-polymorphic headers are skipped (the name
            # cannot be reconstructed without `.{u}`). ONLY theorem/lemma
            # participate: helper_decl_statement folds external binders into a
            # leading ∀ only for theorem/lemma; for def/abbrev/instance it drops
            # the binders, so aliasing them as `theorem DUP : <bare type> :=
            # CANONICAL` would be ill-typed (free variables / a function value).
            can_alias = (
                bool(name)
                and len(statement_norm) >= 16
                and ".{" not in header
                and helper_decl_kind(source) in {"theorem", "lemma"}
            )
            if can_alias and statement_norm in canonical_name_by_statement:
                canonical = canonical_name_by_statement[statement_norm]
                if canonical and canonical != name:
                    result.append(f"theorem {name} : {statement} := {canonical}")
                    continue
            if can_alias:
                canonical_name_by_statement.setdefault(statement_norm, name)
            result.append(source)
        return result

    def verified_helper_blocks_snapshot(self) -> List[str]:
        """Return the currently classified helper context without mutation."""

        return self.verified_helper_blocks(refresh_quality=False)

    def verified_helper_blocks_unique_by_statement(self) -> List[str]:
        """LLM-prompt-safe dedup view of verified_helper_blocks.

        Fix 1 (2026-05-22): two helpers with the same canonical statement key
        are mathematically interchangeable for *citation* purposes, but the
        underlying ``verified_helper_blocks()`` cannot drop either — it feeds
        Lean replay contexts and the ``_support_names_for_proof`` parser,
        which would lose the support edge if a referenced declaration were
        absent from the rendered preamble.

        This deduped variant is safe to use ONLY in contexts that exclusively
        render the LLM-facing inventory (e.g., conversation prompt builders
        that present "available helpers" to the model). Do not use it for
        Lean replay, route-assembly tactic candidates, or any path that
        needs every declaration in scope.

        Prevents a pathology where five identical lemmas were rendered into
        every LLM prompt.
        """
        emitted_statement_keys: Set[str] = set()
        result: List[str] = []
        for block in self.verified_helper_blocks():
            stmt_key = canonical_dossier_statement_key(
                helper_decl_statement(block)
            )
            if stmt_key and stmt_key in emitted_statement_keys:
                continue
            if stmt_key:
                emitted_statement_keys.add(stmt_key)
            result.append(block)
        return result

    def verified_helper_blocks_unique_by_fact(self) -> List[str]:
        """LLM-only helper inventory deduplicated by accepted proposition.

        Unlike the legacy surface-statement view, this uses receipt-bound Lean
        expression identity when available and therefore collapses notation or
        alpha-renaming variants that elaborate to the same proposition in the
        same exact environment.  The full ``verified_helper_blocks()`` remains
        unchanged because Lean replay must keep every declaration name.
        """

        emitted_fact_ids: Set[str] = set()
        result: List[str] = []
        for block in self.verified_helper_blocks():
            helper = self.verified_helpers.get(helper_decl_name(block))
            fact_id = (
                self._verified_fact_identity(helper)
                if helper is not None
                else structural_statement_identity(
                    helper_decl_statement(block),
                    statement_key=canonical_dossier_statement_key(
                        helper_decl_statement(block)
                    ),
                )
            )
            if fact_id and fact_id in emitted_fact_ids:
                continue
            if fact_id:
                emitted_fact_ids.add(fact_id)
            result.append(block)
        return result

    @staticmethod
    def _merge_replay_helper_blocks(
        verified_helpers: Sequence[str],
        fresh_helpers: Sequence[str],
    ) -> List[str]:
        """Merge helper blocks for Lean replay without losing corrections."""

        out: List[str] = []
        by_name: Dict[str, int] = {}
        signatures: Dict[str, str] = {}
        seen_text: Set[str] = set()
        for raw in list(verified_helpers or ()) + list(fresh_helpers or ()):
            block = str(raw or "").strip()
            if not block:
                continue
            name = helper_decl_name(block) or ""
            signature = helper_decl_statement(block) or text_hash(block)
            if name:
                existing_index = by_name.get(name)
                if existing_index is not None:
                    if signatures.get(name) == signature:
                        continue
                    out[existing_index] = block
                    signatures[name] = signature
                    continue
                by_name[name] = len(out)
                signatures[name] = signature
                out.append(block)
                continue
            if block in seen_text:
                continue
            seen_text.add(block)
            out.append(block)
        return out

    def root_replay_integrity_status(
        self,
        *,
        replay_helpers: Optional[Iterable[str]] = None,
        helper_names: Optional[Iterable[str]] = None,
        dependency_helper_names: Optional[Iterable[str]] = None,
        refresh_quality: bool = True,
    ) -> Dict[str, Any]:
        """Return whether replay helpers still match current support hashes."""

        explicit_hash_by_name: Dict[str, str] = {}
        explicit_source_by_name: Dict[str, str] = {}
        # ``verified_helper_blocks`` is the dossier-authorized Lean replay
        # representation.  It may replace an exact-statement duplicate's
        # stored lemma body with a theorem alias to avoid repeatedly
        # elaborating the same proof.  Integrity must therefore recognize
        # both the immutable stored source and this exact current rendering;
        # otherwise the renderer invalidates its own output.
        rendered_hashes_by_name: Dict[str, Set[str]] = {}
        try:
            rendered_sources = self.verified_helper_blocks(
                refresh_quality=refresh_quality,
            )
        except TypeError as exc:
            # Preserve compatibility with lightweight dossier adapters and
            # tests that override the historical zero-argument renderer. The
            # production method accepts the explicit snapshot authority.
            if "refresh_quality" not in str(exc):
                raise
            rendered_sources = self.verified_helper_blocks()
        for rendered_source in rendered_sources:
            rendered_name = helper_decl_name(rendered_source)
            if not rendered_name:
                continue
            hashes = rendered_hashes_by_name.setdefault(rendered_name, set())
            hashes.add(text_hash(rendered_source))
            rendered_artifact = sanitize_lean_artifact_text(rendered_source)
            if rendered_artifact:
                hashes.add(text_hash(rendered_artifact))
        seed_names: List[str] = []

        def add_seed(raw_name: str) -> None:
            key = str(raw_name or "").strip()
            if not key:
                return
            clean = (
                key
                if key in self.verified_helpers
                else self.resolve_verified_helper_name(key)
            )
            candidate = clean or key
            if candidate and candidate not in seed_names:
                seed_names.append(candidate)

        replay_sources = [
            str(block or "").strip()
            for block in list(replay_helpers or ())
            if str(block or "").strip()
        ]
        for source in replay_sources:
            name = helper_decl_name(source)
            if name:
                clean_name = (
                    name
                    if name in self.verified_helpers
                    else self.resolve_verified_helper_name(name)
                )
                candidate_name = clean_name or name
                explicit_hash_by_name[candidate_name] = text_hash(source)
                explicit_source_by_name[candidate_name] = source
                add_seed(name)

        replay_candidate_names = tuple(
            dict.fromkeys(
                [
                    str(name or "").strip()
                    for name in self.verified_helpers
                    if str(name or "").strip()
                ]
                + list(explicit_source_by_name)
            )
        )

        def replay_referenced_names(source: str, *, skip: str = "") -> List[str]:
            if not replay_candidate_names:
                return []
            try:
                from .proof_state import lean_referenced_helper_names

                referenced = lean_referenced_helper_names(
                    str(source or ""),
                    replay_candidate_names,
                    skip=str(skip or "").strip() or None,
                    allow_arbitrary_dot_methods=True,
                )
            except Exception:
                return []
            return [
                name for name in replay_candidate_names if name in referenced
            ]

        for source in replay_sources:
            name = helper_decl_name(source) or ""
            for referenced_name in replay_referenced_names(source, skip=name):
                add_seed(referenced_name)
        for name in list(helper_names or ()):
            add_seed(str(name or ""))
        for name in list(dependency_helper_names or ()):
            add_seed(str(name or ""))

        stale_edges: List[Dict[str, str]] = []
        replay_mismatches: List[Dict[str, str]] = []
        visited: Set[str] = set()

        def helper_support_names(helper: VerifiedHelper) -> List[str]:
            names: List[str] = []
            helper_name = str(getattr(helper, "name", "") or "").strip()
            for raw_name in list(getattr(helper, "support_names", []) or []):
                name = str(raw_name or "").strip()
                if name and name != helper_name and name not in names:
                    names.append(name)
            for raw_name in list(
                getattr(helper, "replay_context_names", []) or []
            ):
                name = str(raw_name or "").strip()
                if name and name != helper_name and name not in names:
                    names.append(name)
            for raw_name in self._referenced_verified_helper_names(
                getattr(helper, "source", ""),
                skip=helper_name,
            ):
                name = str(raw_name or "").strip()
                if name and name != helper_name and name not in names:
                    names.append(name)
            for raw_name in dict(
                getattr(helper, "support_source_hashes", {}) or {}
            ).keys():
                name = str(raw_name or "").strip()
                if name and name != helper_name and name not in names:
                    names.append(name)
            for raw_name in dict(
                getattr(helper, "replay_context_source_hashes", {}) or {}
            ).keys():
                name = str(raw_name or "").strip()
                if name and name != helper_name and name not in names:
                    names.append(name)
            return names

        def visit(raw_name: str) -> None:
            key = str(raw_name or "").strip()
            if not key:
                return
            clean_name = (
                key
                if key in self.verified_helpers
                else self.resolve_verified_helper_name(key)
            )
            helper = self.verified_helpers.get(clean_name)
            if helper is None:
                explicit_source = str(
                    explicit_source_by_name.get(clean_name)
                    or explicit_source_by_name.get(key)
                    or ""
                ).strip()
                if explicit_source:
                    explicit_name = clean_name or key
                    if explicit_name in visited:
                        return
                    visited.add(explicit_name)
                    for support_name in replay_referenced_names(
                        explicit_source,
                        skip=helper_decl_name(explicit_source) or explicit_name,
                    ):
                        visit(support_name)
                    return
                stale_edges.append(
                    {
                        "helper_name": clean_name or key,
                        "support_name": clean_name or key,
                        "recorded_support_hash": explicit_hash_by_name.get(
                            clean_name or key, ""
                        ),
                        "current_support_hash": "",
                        "reason": "missing_current_support",
                    }
                )
                return
            if clean_name in visited:
                return
            visited.add(clean_name)
            explicit_hash = explicit_hash_by_name.get(clean_name)
            helper_hash = str(getattr(helper, "source_hash", "") or "").strip()
            helper_artifact_source = sanitize_lean_artifact_text(
                getattr(helper, "source", "") or ""
            )
            helper_artifact_hash = (
                text_hash(helper_artifact_source) if helper_artifact_source else ""
            )
            helper_hashes = {
                item for item in (helper_hash, helper_artifact_hash) if item
            }
            helper_hashes.update(rendered_hashes_by_name.get(clean_name, set()))
            if explicit_hash and helper_hashes and explicit_hash not in helper_hashes:
                replay_mismatches.append(
                    {
                        "helper_name": clean_name,
                        "current_source_hash": helper_hash or helper_artifact_hash,
                        "current_artifact_source_hash": helper_artifact_hash,
                        "replay_source_hash": explicit_hash,
                    }
                )
            support_hashes = {
                str(name or "").strip(): str(source_hash or "").strip()
                for name, source_hash in dict(
                    getattr(helper, "support_source_hashes", {}) or {}
                ).items()
                if str(name or "").strip() and str(source_hash or "").strip()
            }
            support_hashes.update(
                {
                    str(name or "").strip(): str(source_hash or "").strip()
                    for name, source_hash in dict(
                        getattr(helper, "replay_context_source_hashes", {}) or {}
                    ).items()
                    if str(name or "").strip() and str(source_hash or "").strip()
                }
            )
            for support_name in helper_support_names(helper):
                support_key = (
                    support_name
                    if support_name in self.verified_helpers
                    else self.resolve_verified_helper_name(support_name)
                )
                support = self.verified_helpers.get(support_key)
                recorded_hash = str(
                    support_hashes.get(support_name)
                    or support_hashes.get(support_key)
                    or ""
                ).strip()
                explicit_support_hash = str(
                    explicit_hash_by_name.get(support_key)
                    or explicit_hash_by_name.get(support_name)
                    or ""
                ).strip()
                current_hash = str(
                    getattr(support, "source_hash", "")
                    or explicit_support_hash
                    or ""
                ).strip()
                if support is None and not explicit_support_hash:
                    stale_edges.append(
                        {
                            "helper_name": clean_name,
                            "support_name": support_key or support_name,
                            "recorded_support_hash": recorded_hash,
                            "current_support_hash": "",
                            "reason": "missing_current_support",
                        }
                    )
                    continue
                if recorded_hash and current_hash and recorded_hash != current_hash:
                    stale_edges.append(
                        {
                            "helper_name": clean_name,
                            "support_name": support_key or support_name,
                            "recorded_support_hash": recorded_hash,
                            "current_support_hash": current_hash,
                            "reason": "stale_support_hash",
                        }
                    )
                    continue
                visit(support_key or support_name)

        for name in seed_names:
            visit(name)

        if replay_mismatches or stale_edges:
            return {
                "ready": False,
                "verdict": "root_finalization_stale_helper_support",
                "replay_helper_source_mismatches": replay_mismatches,
                "stale_support_edges": stale_edges,
                "checked_helper_names": sorted(visited),
            }
        return {
            "ready": True,
            "verdict": "root_replay_helper_support_current",
            "checked_helper_names": sorted(visited),
        }

    def root_replay_helper_closure(
        self,
        *,
        replay_helpers: Optional[Iterable[str]] = None,
        support_helper_names: Optional[Iterable[str]] = None,
        refresh_quality: bool = True,
    ) -> List[str]:
        """Return a self-contained helper prefix for replaying the root proof."""

        explicit_blocks = [
            str(helper or "").strip()
            for helper in list(replay_helpers or ())
            if str(helper or "").strip()
        ]
        seed_names: List[str] = []
        for block in explicit_blocks:
            name = helper_decl_name(block)
            for referenced_name in self._referenced_verified_helper_names(
                block,
                skip=name or "",
            ):
                if referenced_name not in seed_names:
                    seed_names.append(referenced_name)
            if name and name not in seed_names:
                seed_names.append(name)
        for name in self._canonical_support_names(support_helper_names or ()):
            if name and name not in seed_names:
                seed_names.append(name)
        route_local_helper_names: Set[str] = set(seed_names)

        closed_blocks: List[str] = []
        visiting: Set[str] = set()
        emitted: Set[str] = set()
        all_by_name = {
            str(name or ""): helper
            for name, helper in self.verified_helpers.items()
            if str(name or "")
        }
        renderable_names = self._verified_helper_renderable_names(all_by_name)

        def visit(name: str) -> bool:
            key = str(name or "").strip()
            clean_name = (
                key
                if key in self.verified_helpers
                else self.resolve_verified_helper_name(key)
            )
            if not clean_name:
                return False
            if clean_name in emitted:
                return True
            if clean_name in visiting:
                return False
            helper = all_by_name.get(clean_name)
            if (
                helper is None
                or clean_name not in renderable_names
                or (
                    not self._verified_helper_context_visible(helper)
                    and clean_name not in route_local_helper_names
                )
            ):
                return False
            integrity_status = self.root_replay_integrity_status(
                helper_names=[clean_name],
                refresh_quality=refresh_quality,
            )
            if not bool(integrity_status.get("ready")):
                return False
            visiting.add(clean_name)
            support_names = self._canonical_support_names(
                list(getattr(helper, "support_names", []) or [])
                + list(getattr(helper, "replay_context_names", []) or [])
                + self._referenced_verified_helper_names(
                    getattr(helper, "source", ""),
                    skip=clean_name,
                )
            )
            if not self._verified_helper_context_visible(helper):
                route_local_helper_names.update(
                    str(support or "").strip()
                    for support in support_names
                    if str(support or "").strip()
                )
            for support in support_names:
                if not visit(str(support or "").strip()):
                    visiting.discard(clean_name)
                    return False
            visiting.discard(clean_name)
            source = str(getattr(helper, "source", "") or "").strip()
            if source:
                closed_blocks.append(source)
                emitted.add(clean_name)
                return True
            return False

        for name in seed_names:
            visit(name)

        explicit_names = {
            helper_decl_name(block) or ""
            for block in explicit_blocks
            if helper_decl_name(block)
        }
        explicit_integrity_ready = bool(
            self.root_replay_integrity_status(
                replay_helpers=explicit_blocks,
                helper_names=explicit_names,
                refresh_quality=refresh_quality,
            ).get("ready")
        )
        explicit_candidates: List[Tuple[str, str, List[str]]] = []
        explicit_available = set(emitted) | explicit_names
        for block in explicit_blocks:
            name = helper_decl_name(block) or ""
            clean_name = (
                name
                if name in self.verified_helpers
                else self.resolve_verified_helper_name(name)
            )
            if clean_name in self.verified_helpers and clean_name not in emitted:
                registered = self.verified_helpers.get(clean_name)
                registered_source = str(
                    getattr(registered, "source", "") or ""
                ).strip()
                registered_artifact = sanitize_lean_artifact_text(
                    registered_source
                )
                exact_hashes = {
                    text_hash(candidate)
                    for candidate in (registered_source, registered_artifact)
                    if candidate
                }
                if (
                    not explicit_integrity_ready
                    or text_hash(block) not in exact_hashes
                ):
                    continue
            missing = self._helper_block_missing_generated_dependencies(
                block,
                helper_name=name,
                available_names=explicit_available,
            )
            if missing:
                continue
            deps = [
                dep
                for dep in self._referenced_generated_helper_names(block, skip=name)
                if dep in explicit_names and dep != name
            ]
            explicit_candidates.append((name, block, deps))
        ordered_explicit: List[str] = []
        emitted_explicit: Set[str] = set()
        pending_explicit = list(explicit_candidates)
        while pending_explicit:
            progressed = False
            next_pending: List[Tuple[str, str, List[str]]] = []
            for name, block, deps in pending_explicit:
                if all(dep in emitted or dep in emitted_explicit for dep in deps):
                    ordered_explicit.append(block)
                    if name:
                        emitted_explicit.add(name)
                    progressed = True
                else:
                    next_pending.append((name, block, deps))
            if not progressed:
                break
            pending_explicit = next_pending

        merged = self._merge_replay_helper_blocks(closed_blocks, ordered_explicit)
        if refresh_quality and len(merged) > len(explicit_blocks):
            self.increment_tool_metric(
                "mini_root_certificate_helper_closure_expanded",
                1,
            )
        return merged

    def _root_proof_certificate(
        self,
        *,
        proof: str,
        replay_helpers: Sequence[str],
        support_helper_names: Sequence[str],
        metadata: Optional[Dict[str, Any]] = None,
    ) -> Dict[str, Any]:
        helper_names = [
            name
            for block in replay_helpers
            for name in [helper_decl_name(block)]
            if name
        ]
        helper_hashes = [text_hash(block) for block in replay_helpers]
        return {
            "schema_version": 1,
            "theorem_name": self.theorem_name,
            "root_statement": self.root_statement,
            "root_statement_hash": text_hash(self.root_statement),
            # Proof authority is meaningful only in the checker environment
            # in which the root was accepted.  Fan-in validates this binding
            # before recovering a proof from a failed or abandoned task.
            "target_environment_hash": str(
                self.current_lean_environment_hash or ""
            ).strip(),
            "proof": str(proof or ""),
            "proof_hash": text_hash(proof),
            "replay_helpers": list(replay_helpers),
            "replay_helper_names": helper_names,
            "replay_helper_source_hashes": helper_hashes,
            "replay_helper_count": len(replay_helpers),
            "support_helper_names": [
                str(name or "").strip()
                for name in support_helper_names
                if str(name or "").strip()
            ],
            **dict(metadata or {}),
        }

    def root_proof_finalization_receipt_hash(self) -> str:
        certificate = self.root_proof_certificate
        proof = str(self.final_proof or "").strip()
        if not proof or not isinstance(certificate, Mapping):
            return ""
        payload = {
            "schema": "mini_root_proof_finalization_receipt_v1",
            "theorem_name": str(self.theorem_name or "").strip(),
            "root_statement": str(self.root_statement or "").strip(),
            # Bind the receipt to the immutable checker environment in which
            # the proof was finalized. The dossier may later move to a
            # validated monotone descendant; fan-in checks that compatibility
            # separately without changing this receipt identity.
            "target_environment_hash": str(
                certificate.get("target_environment_hash") or ""
            ).strip(),
            "final_proof": proof,
            "final_proof_hash": str(self.final_proof_hash or "").strip(),
            "final_replay_helpers": list(self.final_replay_helpers or ()),
            "root_proof_certificate": dict(certificate),
        }
        encoded = json.dumps(
            payload,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            default=str,
        ).encode("utf-8")
        return hashlib.sha256(encoded).hexdigest()

    def record_root_proof_finalization_receipt(self) -> str:
        receipt_hash = self.root_proof_finalization_receipt_hash()
        if not receipt_hash:
            raise ValueError("root proof finalization receipt lacks an artifact")
        self._root_proof_finalization_receipts.add(receipt_hash)
        return receipt_hash

    def has_root_proof_finalization_receipt(self) -> bool:
        receipt_hash = self.root_proof_finalization_receipt_hash()
        return bool(
            receipt_hash
            and receipt_hash in self._root_proof_finalization_receipts
        )

    def proposed_helper_blocks(self) -> List[str]:
        return [item.source for item in self.proposed_helpers.values()]

    def has_helper(self, name: str) -> bool:
        return bool(self._equivalent_helper_registry_name(self.verified_helpers, name))

    def has_proposed_helper(self, name: str) -> bool:
        return bool(self._equivalent_helper_registry_name(self.proposed_helpers, name))

    @staticmethod
    def _equivalent_helper_registry_name(
        registry: Mapping[str, Any],
        name: str,
    ) -> str:
        clean = str(name or "").strip()
        if not clean:
            return ""
        if clean in registry:
            return clean
        canonical = canonical_lean_identifier(clean)
        return next(
            (
                str(candidate or "").strip()
                for candidate in registry
                if canonical_lean_identifier(str(candidate or "").strip())
                == canonical
            ),
            "",
        )

    def _canonical_support_names(self, names: Iterable[str]) -> List[str]:
        out: List[str] = []
        for raw_name in list(names or ()):
            key = str(raw_name or "").strip()
            clean = (
                key
                if key in self.verified_helpers
                else self.resolve_verified_helper_name(key)
            )
            if not clean or clean not in self.verified_helpers or clean in out:
                continue
            out.append(clean)
        return out

    @staticmethod
    def _generated_helper_reference_root(name: str) -> str:
        clean = str(name or "").strip()
        if not clean:
            return ""
        segments = clean.split(".")
        if len(segments) == 1:
            return clean
        method_suffixes = {
            "left",
            "right",
            "mp",
            "mpr",
            "fst",
            "snd",
            "symm",
            "trans",
            "property",
            "val",
        }
        return segments[0] if segments[1] in method_suffixes else clean

    @classmethod
    def _generated_helper_reference_looks_local(cls, name: str) -> bool:
        root = cls._generated_helper_reference_root(name)
        if not root:
            return False
        return bool(_GENERATED_HELPER_REFERENCE_RE.fullmatch(root))

    @staticmethod
    def _helper_decl_parameter_names(source: str) -> Set[str]:
        parsed = graph_helper_decl_header(str(source or ""))
        if parsed is None:
            return set()
        _kind, _name, tail = parsed
        header_end = len(tail)
        assign_index = tail.find(":=")
        if assign_index >= 0:
            header_end = assign_index
        where_match = re.search(r"\bwhere\b", tail)
        if where_match is not None:
            header_end = min(header_end, where_match.start())
        header = tail[:header_end]
        names: Set[str] = set()
        close_for = {"(": ")", "{": "}", "[": "]"}
        index = 0
        while index < len(header):
            opener = header[index]
            closer = close_for.get(opener)
            if closer is None:
                index += 1
                continue
            depth = 1
            end = index + 1
            while end < len(header) and depth:
                if header[end] == opener:
                    depth += 1
                elif header[end] == closer:
                    depth -= 1
                end += 1
            if depth:
                break
            group = header[index + 1 : end - 1]
            if ":" in group:
                lhs = group.split(":", 1)[0]
                for raw_name in re.findall(
                    r"«[^»]+»|[A-Za-z_][A-Za-z0-9_']*",
                    lhs,
                ):
                    clean = raw_name.strip("«»").strip()
                    if clean and clean != "_":
                        names.add(clean)
            index = end
        return names

    def _referenced_generated_helper_names(
        self,
        source: str,
        *,
        skip: str = "",
    ) -> List[str]:
        skip_name = str(skip or "").strip()
        source_text = str(source or "")
        try:
            from .proof_state import (
                _strip_lean_comments_and_strings,
                lean_referenced_helper_names,
            )
        except Exception:
            _strip_lean_comments_and_strings = None
            lean_referenced_helper_names = None
        scan_text = source_text
        if _strip_lean_comments_and_strings is not None:
            try:
                scan_text = _strip_lean_comments_and_strings(source_text)
            except Exception:
                scan_text = source_text
        out: List[str] = []
        for match in _GENERATED_HELPER_REFERENCE_RE.finditer(scan_text):
            raw_name = str(match.group(1) or "").strip()
            if canonical_lean_identifier(raw_name) == canonical_lean_identifier(
                skip_name
            ):
                continue
            name = self._generated_helper_reference_root(raw_name)
            if not name or name == skip_name or name in out:
                continue
            out.append(name)
        if out:
            bound_parameters = self._helper_decl_parameter_names(source_text)
            out = [name for name in out if name not in bound_parameters]
        if out and lean_referenced_helper_names is not None:
            try:
                referenced = lean_referenced_helper_names(
                    source_text,
                    out,
                    skip=skip_name or None,
                    allow_arbitrary_dot_methods=True,
                )
            except Exception:
                referenced = set(out)
            out = [name for name in out if name in referenced]
        return out

    def _verified_helper_missing_generated_dependencies(
        self,
        helper: VerifiedHelper,
        *,
        available_names: Iterable[str],
    ) -> List[str]:
        deps = self._verified_helper_generated_dependencies(helper)
        available = {
            str(name or "").strip()
            for name in list(available_names or [])
            if str(name or "").strip()
        }
        return [name for name in deps if name not in available]

    def _verified_helper_generated_dependencies(
        self,
        helper: VerifiedHelper,
    ) -> List[str]:
        helper_name = str(getattr(helper, "name", "") or "").strip()
        deps: List[str] = []
        for raw_name in list(getattr(helper, "support_names", []) or []):
            root = self._generated_helper_reference_root(str(raw_name or ""))
            if (
                root
                and root != helper_name
                and root not in deps
            ):
                deps.append(root)
        for raw_name in list(getattr(helper, "replay_context_names", []) or []):
            root = self._generated_helper_reference_root(str(raw_name or ""))
            if (
                root
                and root != helper_name
                and root not in deps
            ):
                deps.append(root)
        for raw_name in self._referenced_generated_helper_names(
            getattr(helper, "source", ""),
            skip=helper_name,
        ):
            root = self._generated_helper_reference_root(raw_name)
            if root and root != helper_name and root not in deps:
                deps.append(root)
        return deps

    def _verified_helper_renderable_names(
        self,
        by_name: Dict[str, VerifiedHelper],
    ) -> Set[str]:
        """Return helpers whose generated dependencies are transitively renderable."""

        pending: Dict[str, VerifiedHelper] = dict(by_name)
        renderable: Set[str] = set()
        while pending:
            progressed = False
            for name, helper in list(pending.items()):
                generated_deps = self._verified_helper_generated_dependencies(helper)
                if all(dep in renderable for dep in generated_deps):
                    renderable.add(name)
                    pending.pop(name, None)
                    progressed = True
            if not progressed:
                break
        return renderable

    def _helper_block_missing_generated_dependencies(
        self,
        block: str,
        *,
        helper_name: str = "",
        available_names: Iterable[str],
    ) -> List[str]:
        available = {
            str(name or "").strip()
            for name in list(available_names or [])
            if str(name or "").strip()
        }
        missing: List[str] = []
        for raw_name in self._referenced_generated_helper_names(
            str(block or ""),
            skip=str(helper_name or "").strip(),
        ):
            root = self._generated_helper_reference_root(raw_name)
            if root and root not in available and root not in missing:
                missing.append(root)
        return missing

    def _referenced_verified_helper_names(
        self,
        source: str,
        *,
        skip: str = "",
    ) -> List[str]:
        available_names = [
            str(name or "").strip()
            for name in self.verified_helpers
            if str(name or "").strip() and str(name or "").strip() != str(skip or "")
        ]
        if not available_names:
            return []
        try:
            from .proof_state import lean_referenced_helper_names
        except Exception:
            return []
        try:
            referenced = lean_referenced_helper_names(
                str(source or ""),
                available_names,
                skip=str(skip or "").strip() or None,
                allow_arbitrary_dot_methods=True,
            )
        except Exception:
            return []
        return [name for name in available_names if name in referenced]

    def resolve_verified_helper_name(self, name: str) -> str:
        """Resolve a possibly-aliased helper name to its canonical verified name.

        If ``name`` was registered as a statement-equivalent alias of an earlier
        verified helper (see ``record_verified_helper``), return the canonical
        name. Otherwise return ``name`` unchanged. Returns the input verbatim
        for names that do not appear in either the verified helper map or the
        alias map — callers can then decide whether the lookup failed.
        """
        key = str(name or "").strip()
        if not key:
            return key
        equivalent = self._equivalent_helper_registry_name(
            self.verified_helpers,
            key,
        )
        resolved = equivalent or key
        return self.verified_helper_statement_aliases.get(resolved, resolved)

    @staticmethod
    def _invalidation_target_environment_hash(provenance: Any) -> str:
        if not isinstance(provenance, dict):
            return ""
        return str(provenance.get("target_environment_hash") or "").strip()

    def invalidated_statement_reason(
        self,
        statement: str,
        *,
        target_environment_hash: str = "",
    ) -> str:
        key = canonical_dossier_statement_key(statement)
        if not key:
            return ""
        expected_environment_hash = str(
            target_environment_hash or self.current_lean_environment_hash or ""
        ).strip()
        exact = _exact_statement_text(statement)
        statement_full_expr_hash = _exact_statement_full_expr_hash(
            self, exact, expected_environment_hash
        )
        for authority in dict(self.mini_authoritative_negations or {}).values():
            if not isinstance(authority, Mapping):
                continue
            recorded_environment_hash = str(
                authority.get("target_environment_hash") or ""
            ).strip()
            if recorded_environment_hash != expected_environment_hash:
                continue
            exact_match = _exact_statement_text(authority.get("statement")) == exact
            full_expr_match = bool(
                statement_full_expr_hash
                and statement_full_expr_hash
                == str(authority.get("target_full_expr_hash") or "").strip()
            )
            if exact_match or full_expr_match:
                return str(authority.get("reason") or "")
        return ""

    def reconcile_invalidated_graph_targets(self) -> Dict[str, List[str]]:
        """Apply every currently authoritative invalidation to late aliases.

        Graph projection is mutable and may create an exact target or route
        after the certificate was first recorded. This idempotent closure is
        safe at projection and scheduler boundaries; only invalidations whose
        typed authority survived the current process are present in the map.
        """

        graph = self.proof_graph
        if graph is None:
            return {"terminalized_node_ids": [], "retired_route_ids": []}
        before_terminal = {
            node.node_id
            for node in graph.nodes.values()
            if node.status in {"failed", "rejected", "blocked"}
            and bool((node.metadata or {}).get("authoritative_falsification_terminal"))
        }
        before_retired = {
            route.node_id
            for route in graph.nodes_by_kind("strategy_route")
            if bool(
                (route.metadata or {}).get("route_retired")
                or (route.metadata or {}).get("route_dependency_contradicted")
            )
        }
        for authority in list(self.mini_authoritative_negations.values()):
            if not isinstance(authority, Mapping):
                continue
            statement = _exact_statement_text(authority.get("statement"))
            clean_key = canonical_dossier_statement_key(statement)
            if not clean_key:
                continue
            reason = str(authority.get("reason") or "")
            target_environment_hash = str(
                authority.get("target_environment_hash") or ""
            ).strip()
            if not target_environment_hash:
                continue
            _purge_proposed_helpers_for_statement_key(
                self,
                clean_key,
                reason=str(reason or ""),
                target_environment_hash=target_environment_hash,
            )
            _retire_route_contracts_for_invalidated_statement_key(
                self,
                clean_key,
                reason=str(reason or ""),
                target_environment_hash=target_environment_hash,
            )
        after_terminal = {
            node.node_id
            for node in graph.nodes.values()
            if node.status in {"failed", "rejected", "blocked"}
            and bool((node.metadata or {}).get("authoritative_falsification_terminal"))
        }
        after_retired = {
            route.node_id
            for route in graph.nodes_by_kind("strategy_route")
            if bool(
                (route.metadata or {}).get("route_retired")
                or (route.metadata or {}).get("route_dependency_contradicted")
            )
        }
        return {
            "terminalized_node_ids": sorted(after_terminal - before_terminal),
            "retired_route_ids": sorted(after_retired - before_retired),
        }

    def record_invalidated_statement(
        self,
        statement: str,
        reason: str,
        *,
        provenance: Optional[Dict[str, Any]] = None,
    ) -> None:
        key = canonical_dossier_statement_key(statement)
        if not key:
            return
        reason_text = str(reason or "")
        authority_id = (
            str(provenance.get("authority_id") or "").strip()
            if isinstance(provenance, Mapping)
            else ""
        )
        has_live_authority = bool(
            authority_id
            and authority_id in self.mini_authoritative_negations
            and str((provenance or {}).get("kind") or "")
            == "fresh_lean_certificate"
        )
        existing_reason = self.mini_recursive_invalidated_statement_reasons.get(key)
        target_environment_hash = self._invalidation_target_environment_hash(
            provenance
            if isinstance(provenance, dict)
            else self.mini_recursive_invalidation_provenance.get(key)
        )
        if not has_live_authority:
            # Reason-only and verified-helper observations are useful planner
            # diagnostics, but this historical map is consumed by scheduler
            # and planner filters. Storing them here would silently turn prose
            # into liveness authority, so leave the authoritative maps alone.
            return
        if existing_reason == reason_text and (
            provenance is None
            or self.mini_recursive_invalidation_provenance.get(key) == provenance
        ):
            # Idempotence applies to the durable fact, not to its closure over
            # mutable graph projections.  A missing obligation or route can be
            # created after the first certificate was recorded (checkpoint
            # replay and proof-state promotion both do this), so re-sweep exact
            # aliases even when the invalidation record itself is unchanged.
            _preserve_authoritative_reformulation_candidates(
                self,
                key,
                reason=reason_text,
                target_environment_hash=target_environment_hash,
            )
            _record_authoritative_proof_idea_claim_invalidations(
                self,
                key,
                reason=reason_text,
                target_environment_hash=target_environment_hash,
                provenance=(
                    provenance
                    if isinstance(provenance, Mapping)
                    else self.mini_recursive_invalidation_provenance.get(key)
                ),
            )
            _purge_proposed_helpers_for_statement_key(
                self,
                key,
                reason=reason,
                target_environment_hash=target_environment_hash,
            )
            _retire_route_contracts_for_invalidated_statement_key(
                self,
                key,
                reason=reason,
                target_environment_hash=target_environment_hash,
            )
            return
        self.mini_recursive_invalidated_statement_reasons[key] = reason_text
        if isinstance(provenance, dict) and str(provenance.get("kind") or ""):
            self.mini_recursive_invalidation_provenance[key] = copy.deepcopy(
                provenance
            )
        _preserve_authoritative_reformulation_candidates(
            self,
            key,
            reason=reason_text,
            target_environment_hash=target_environment_hash,
        )
        _record_authoritative_proof_idea_claim_invalidations(
            self,
            key,
            reason=reason_text,
            target_environment_hash=target_environment_hash,
            provenance=(
                provenance
                if isinstance(provenance, Mapping)
                else self.mini_recursive_invalidation_provenance.get(key)
            ),
        )
        _purge_proposed_helpers_for_statement_key(
            self,
            key,
            reason=reason,
            target_environment_hash=target_environment_hash,
        )
        _retire_route_contracts_for_invalidated_statement_key(
            self,
            key,
            reason=reason,
            target_environment_hash=target_environment_hash,
        )

    def record_falsification_report(self, report: Any) -> bool:
        """Persist a report and apply only its authoritative certificate.

        Returns ``True`` exactly when the report contains an axiom-audited
        proof of the full negation.  Concrete samples, external solver output,
        structural heuristics, and unaudited Lean checks remain advisory.
        """

        to_record = getattr(report, "to_record", None)
        if not callable(to_record):
            raise TypeError("falsification report must provide to_record()")
        record = copy.deepcopy(to_record())
        if not isinstance(record, dict):
            raise TypeError("falsification report record must be a mapping")
        from .mini_falsification import (
            authoritative_certificate_record_is_valid,
            falsification_report_record_is_valid,
        )
        from .mini_falsification.certificate import (
            authoritative_certificate_record_has_process_receipt,
        )

        if not falsification_report_record_is_valid(record):
            raise ValueError("falsification report failed integrity checks")
        report_statement = str(record.get("statement") or "").strip()
        report_kind = str(record.get("target_kind") or "").strip()
        target_environment_hash = str(
            self.current_lean_environment_hash or ""
        ).strip()
        nested_authoritative_records = [
            copy.deepcopy(finding.get("certificate"))
            for finding in list(record.get("findings") or [])
            if isinstance(finding, dict)
            and str(finding.get("outcome") or "") == "refuted"
            and isinstance(finding.get("certificate"), dict)
            and bool(finding["certificate"].get("authoritative"))
        ]
        candidate_certificate_record: Optional[Dict[str, Any]] = None
        if nested_authoritative_records:
            if not target_environment_hash:
                raise ValueError(
                    "authoritative falsification requires a bound target environment"
                )
            candidate_certificate = getattr(
                report,
                "authoritative_refutation",
                None,
            )
            candidate_to_record = getattr(candidate_certificate, "to_record", None)
            if not callable(candidate_to_record):
                return False
            try:
                materialized_candidate = copy.deepcopy(candidate_to_record())
            except Exception:
                return False
            if not isinstance(materialized_candidate, dict):
                return False
            if not authoritative_certificate_record_is_valid(materialized_candidate):
                return False
            matching_nested_records = [
                nested
                for nested in nested_authoritative_records
                if nested == materialized_candidate
            ]
            if not matching_nested_records:
                return False
            candidate_certificate_record = materialized_candidate
            if not authoritative_certificate_record_has_process_receipt(
                candidate_certificate_record,
                target_environment_hash=target_environment_hash,
            ):
                # A trust enum plus self-consistent hashes is only data, not
                # proof that Lean ran. Reject before recording even advisory
                # ledger state so a forged envelope has no effects.
                return False
        report_targets_root = _statements_share_bound_lean_identity(
            self,
            report_statement,
            self.root_statement,
            target_environment_hash,
        )
        if report_kind == "root" and not report_targets_root:
            raise ValueError("root falsification report does not target dossier root")
        report_hash = str(record.get("report_hash") or "").strip()
        if not report_hash:
            raise ValueError("falsification report lacks a content hash")
        is_new_report = not any(
            str(item.get("report_hash") or "") == report_hash
            for item in self.mini_falsification_ledger
            if isinstance(item, dict)
        )
        if is_new_report:
            self.mini_falsification_ledger.append(record)
            _sort_falsification_ledger_by_evidence_time(
                self.mini_falsification_ledger
            )
            findings = [
                item
                for item in list(record.get("findings") or [])
                if isinstance(item, dict)
            ]
            self.increment_tool_metric("mini_falsification_reports", 1)
            self.increment_tool_metric("mini_falsification_engine_runs", len(findings))
            self.increment_tool_metric(
                "mini_falsification_candidates",
                sum(len(item.get("candidates") or []) for item in findings),
            )
            self.increment_tool_metric(
                "mini_falsification_transient_failures",
                sum(item.get("outcome") == "transient_failure" for item in findings),
            )
        report_environment_hash = str(record.get("environment_hash") or "").strip()
        for finding in list(record.get("findings") or []):
            if not isinstance(finding, dict):
                continue
            engine = str(finding.get("engine") or "").strip()
            cursor = finding.get("cursor")
            if not engine or not isinstance(cursor, dict) or not cursor:
                # Non-empty TRANSIENT cursors are now persisted too: they
                # carry the completed prefix of a watchdog-cancelled batch,
                # and the monotone merge below already prevents regressions
                # (empty transient cursors are still skipped above).
                continue
            validated_cursor = _validated_falsification_cursor(
                cursor,
                engine=engine,
            )
            if validated_cursor is None or not _recipe_repair_cursor_matches_finding(
                finding,
                validated_cursor,
            ):
                continue
            target_cursors = _falsification_cursor_target_entry(
                self,
                report_statement,
                falsification_environment_hash=report_environment_hash,
                create=True,
            )
            if target_cursors is None:
                continue
            _merge_falsification_cursor(
                target_cursors,
                engine=engine,
                cursor=validated_cursor,
            )

        if candidate_certificate_record is None:
            return False
        certificate_record = candidate_certificate_record
        statement = str(certificate_record.get("statement") or "").strip()
        if not statement:
            raise ValueError("authoritative certificate lacks a statement")
        if not (
            statement == report_statement
            and str(certificate_record.get("environment_hash") or "").strip()
            == report_environment_hash
        ):
            raise ValueError("authoritative certificate is not linked to its report")
        target_full_expr_hash = _exact_statement_full_expr_hash(
            self, statement, target_environment_hash
        )
        conflicting_helpers = _verified_helpers_conflicting_with_falsification(
            self,
            statement,
            target_environment_hash,
            target_full_expr_hash=target_full_expr_hash,
        )
        root_exact = _exact_statement_text(self.root_statement)
        root_match = _statements_share_bound_lean_identity(
            self, statement, root_exact, target_environment_hash
        )
        if conflicting_helpers or (root_match and self.final_proof):
            _record_falsification_trust_boundary_conflict(
                self,
                certificate_hash=str(
                    certificate_record.get("certificate_hash") or ""
                ),
            )
            return False
        reason = (
            "Lean proved and axiom-audited the full negation; certificate "
            + str(certificate_record.get("certificate_hash") or "")[:16]
        )
        authority = {
            "schema_version": 1,
            "statement": statement,
            "statement_hash": hashlib.sha256(statement.encode("utf-8")).hexdigest(),
            "target_environment_hash": target_environment_hash,
            "target_full_expr_hash": target_full_expr_hash,
            "certificate_hash": str(
                certificate_record.get("certificate_hash") or ""
            ).strip(),
            "report_hash": report_hash,
            "reason": reason,
        }
        authority_id = _authoritative_negation_id(authority)
        authority["authority_id"] = authority_id
        self.mini_authoritative_negations[authority_id] = copy.deepcopy(authority)
        if root_match:
            self.root_disproof_certificate = copy.deepcopy(certificate_record)
        self.record_invalidated_statement(
            statement,
            reason,
            provenance={
                "kind": "fresh_lean_certificate",
                "certificate": copy.deepcopy(certificate_record),
                "report_hash": report_hash,
                "authority_id": authority_id,
                "statement": statement,
                "target_full_expr_hash": authority["target_full_expr_hash"],
                # This is the Lean statement environment, not the
                # falsification-service runtime/policy environment hash.
                "target_environment_hash": target_environment_hash,
            },
        )
        self.mini_falsification_pending_certificates = [
            item
            for item in self.mini_falsification_pending_certificates
            if str(dict(item.get("certificate") or {}).get("certificate_hash") or "")
            != str(certificate_record.get("certificate_hash") or "")
        ]
        if is_new_report:
            self.increment_tool_metric(
                "mini_falsification_authoritative_refutations", 1
            )
        return True

    def falsification_cursors_for_statement(
        self, statement: str, *, environment_hash: str = ""
    ) -> Dict[str, Dict[str, Any]]:
        expected = str(environment_hash or "").strip()
        merged: Dict[str, Any] = {}
        matched_environment = ""
        for entry in _falsification_cursor_entries_for_statement(self, statement):
            actual = str(entry.get("__environment_hash__") or "").strip()
            if expected and actual != expected:
                continue
            if matched_environment and actual != matched_environment:
                # Two elaborated aliases produced progress in different
                # falsification worlds. They cannot be ordered safely.
                return {}
            matched_environment = actual
            for engine, cursor in entry.items():
                if str(engine).startswith("__") or not isinstance(cursor, dict):
                    continue
                _merge_falsification_cursor(
                    merged,
                    engine=str(engine),
                    cursor=cursor,
                )
        return {
            str(engine): copy.deepcopy(cursor)
            for engine, cursor in merged.items()
            if isinstance(cursor, dict)
        }

    def unpromoted_refutation_candidates_for_statement(
        self,
        statement: str,
    ) -> List[Dict[str, Any]]:
        """Return integrity-checked counterexample hints lacking full authority.

        These records may steer search away from a suspect route, but callers
        must never bank mathematical invalidity from them. Only
        ``record_falsification_report`` promotes an axiom-audited full-negation
        certificate into durable invalidation.
        """

        key = canonical_dossier_statement_key(statement)
        if not key:
            return []
        # Authoritative invalidation always dominates advisory route hints,
        # including a mixed report that carries both kinds of evidence.
        if self.invalidated_statement_reason(statement):
            return []
        # Root falsification is an advisory preflight for the theorem itself,
        # never a reason to suppress the root-assembly lane. Only an
        # authoritative certificate may invalidate the root.
        if key == canonical_dossier_statement_key(self.root_statement):
            return []
        # A currently verified exact helper is stronger, fresh Lean evidence
        # than any historical unpromoted counterexample hint.
        if any(
            canonical_dossier_statement_key(
                helper_decl_statement(getattr(helper, "source", "") or "")
            )
            == key
            for helper in self.verified_helpers.values()
        ):
            return []
        raw_report = _latest_helper_falsification_report_for_key(
            self.mini_falsification_ledger,
            key,
        )
        if raw_report is None:
            return []
        # ``started_at`` and the deterministic hash tie-breaker are both
        # covered by report_hash. Branch propagation order is not evidence
        # order and must never resurrect an older advisory candidate.
        matches: List[Dict[str, Any]] = []
        for finding in raw_report.get("findings") or ():
            if (
                not isinstance(finding, Mapping)
                or not list(finding.get("candidates") or ())
            ):
                continue
            certificate = finding.get("certificate")
            if isinstance(certificate, Mapping) and bool(
                certificate.get("authoritative")
            ):
                continue
            matches.append(
                {
                    "report_hash": str(raw_report.get("report_hash") or ""),
                    "engine": str(finding.get("engine") or ""),
                    "reason": str(finding.get("reason") or ""),
                    "candidates": copy.deepcopy(
                        list(finding.get("candidates") or ())
                    ),
                }
            )
        return matches

    def lean_checked_unpromoted_refutation_candidates_for_statement(
        self,
        statement: str,
    ) -> List[Dict[str, Any]]:
        """Return advisory candidates backed by a concrete Lean check.

        Structural/prose heuristics remain visible in the audit ledger but
        cannot preempt proof work or be described to an LLM as Lean-checked.
        The presence of ``instance_lean_output`` is the receipt emitted by the
        shared witness checker; its value may legitimately be empty on a
        successful quiet Lean process.
        """

        checked: List[Dict[str, Any]] = []
        for finding in self.unpromoted_refutation_candidates_for_statement(
            statement
        ):
            candidates = []
            for candidate in list(finding.get("candidates") or ()):
                if not isinstance(candidate, Mapping):
                    continue
                metadata = candidate.get("metadata")
                if not isinstance(metadata, Mapping):
                    continue
                if "instance_lean_output" not in metadata:
                    continue
                if not str(candidate.get("concrete_statement") or "").strip():
                    continue
                candidates.append(copy.deepcopy(dict(candidate)))
            if not candidates:
                continue
            record = copy.deepcopy(dict(finding))
            record["candidates"] = candidates
            checked.append(record)
        return checked

    def active_unpromoted_refutation_frontier(
        self,
    ) -> Dict[str, Tuple[str, ...]]:
        """Semantic active-quarantine identity for scheduler fixed points.

        Report envelopes are intentionally excluded: a repeated transient,
        unsupported, inconclusive, or byte-equivalent candidate campaign must
        not manufacture fresh scheduler progress merely by acquiring a new
        wall-clock timestamp. A newer clearing report removes the statement
        key; a genuinely different candidate hash changes its identity.
        """

        root_key = canonical_dossier_statement_key(self.root_statement)
        verified_keys = {
            canonical_dossier_statement_key(
                helper_decl_statement(getattr(helper, "source", "") or "")
            )
            for helper in self.verified_helpers.values()
        }
        invalidated_keys = set(
            self.mini_recursive_invalidated_statement_reasons
        )
        statement_keys = {
            canonical_dossier_statement_key(
                str(report.get("statement") or "")
            )
            for report in self.mini_falsification_ledger
            if isinstance(report, Mapping)
            and str(report.get("target_kind") or "") == "helper"
        }
        frontier: Dict[str, Tuple[str, ...]] = {}
        for key in sorted(
            item
            for item in statement_keys
            if (
                item
                and item != root_key
                and item not in verified_keys
                and item not in invalidated_keys
            )
        ):
            report = _latest_helper_falsification_report_for_key(
                self.mini_falsification_ledger,
                key,
            )
            if report is None:
                continue
            identities = {
                (
                    str(finding.get("engine") or "")
                    + ":"
                    + text_hash(
                        json.dumps(
                            {
                                "engine": str(
                                    candidate.get("engine")
                                    or finding.get("engine")
                                    or ""
                                ),
                                "witness_terms": [
                                    str(item or "").strip()
                                    for item in candidate.get("witness_terms") or ()
                                ],
                                "concrete_statement": (
                                    canonical_dossier_statement_key(
                                        str(
                                            candidate.get("concrete_statement")
                                            or ""
                                        )
                                    )
                                    if str(
                                        candidate.get("concrete_statement") or ""
                                    ).strip()
                                    else ""
                                ),
                                "structural_obstruction": (
                                    {
                                        "kind": str(
                                            dict(
                                                candidate.get("metadata") or {}
                                            ).get("obstruction_kind")
                                            or ""
                                        ),
                                        "detail": str(
                                            dict(
                                                candidate.get("metadata") or {}
                                            ).get("obstruction_detail")
                                            or ""
                                        ),
                                    }
                                    if not list(
                                        candidate.get("witness_terms") or ()
                                    )
                                    and not str(
                                        candidate.get("concrete_statement") or ""
                                    ).strip()
                                    and (
                                        "obstruction_kind"
                                        in dict(candidate.get("metadata") or {})
                                        or "obstruction_detail"
                                        in dict(candidate.get("metadata") or {})
                                    )
                                    else None
                                ),
                            },
                            sort_keys=True,
                            separators=(",", ":"),
                            ensure_ascii=True,
                        )
                    )
                )
                for finding in report.get("findings") or ()
                if isinstance(finding, Mapping)
                and not (
                    isinstance(finding.get("certificate"), Mapping)
                    and bool(finding["certificate"].get("authoritative"))
                )
                for candidate in finding.get("candidates") or ()
                if isinstance(candidate, Mapping)
            }
            if identities:
                frontier[key] = tuple(sorted(identities))
        return frontier

    def record_certificate_replay_disposition(
        self,
        *,
        certificate_hash: str,
        environment_hash: str,
        policy_hash: str,
        reason: str = "",
    ) -> Dict[str, Any]:
        from .mini_falsification.model import content_hash

        certificate_hash = str(certificate_hash or "").strip()
        environment_hash = str(environment_hash or "").strip()
        policy_hash = str(policy_hash or "").strip()
        if not all(
            re.fullmatch(r"[0-9a-f]{64}", item)
            for item in (certificate_hash, environment_hash, policy_hash)
        ):
            raise ValueError("certificate replay disposition has invalid identity")
        record = {
            "schema_version": _CERTIFICATE_REPLAY_DISPOSITION_SCHEMA,
            "status": "definitive_rejection",
            "certificate_hash": certificate_hash,
            "environment_hash": environment_hash,
            "policy_hash": policy_hash,
            "reason": str(reason or "")[:500],
        }
        record["disposition_hash"] = content_hash(record)
        disposition_id = _certificate_replay_disposition_id(
            certificate_hash, environment_hash, policy_hash
        )
        self.mini_falsification_certificate_replay_dispositions[
            disposition_id
        ] = record
        return copy.deepcopy(record)

    def certificate_replay_is_suppressed(
        self,
        *,
        certificate_hash: str,
        environment_hash: str,
        policy_hash: str,
    ) -> bool:
        disposition_id = _certificate_replay_disposition_id(
            certificate_hash, environment_hash, policy_hash
        )
        record = self.mini_falsification_certificate_replay_dispositions.get(
            disposition_id
        )
        return bool(
            _certificate_replay_disposition_is_valid(record)
            and str(record.get("certificate_hash") or "")
            == str(certificate_hash or "")
            and str(record.get("environment_hash") or "")
            == str(environment_hash or "")
            and str(record.get("policy_hash") or "")
            == str(policy_hash or "")
        )

    def record_proposed_helper(
        self,
        source: str,
        *,
        phase: str,
        turn_index: int,
    ) -> Optional[ProposedHelper]:
        """Bank a helper the prover proposed but did not verify.

        Returns the recorded ``ProposedHelper`` on success, or ``None`` if
        the source has no decl name, no parseable statement, is already
        verified, or is answer-unsafe (mentions a ``*_solution``
        placeholder — same safety bar as ``record_verified_helper``).

        Idempotent on name: re-proposing the same name updates the
        statement/source/phase/turn_index to the freshest value.
        """
        src = str(source or "").strip()
        if not src:
            return None
        name = helper_decl_name(src)
        if not name:
            return None
        # Already-verified helpers are not "proposed" — drop silently.
        if name in self.verified_helpers:
            return None
        if is_answer_unsafe_helper_source(src, **self._answer_safety_kwargs()):
            return None
        statement = helper_decl_statement(src)
        if not statement:
            self.increment_tool_metric(
                "mini_proposed_helpers_rejected_malformed_statement",
                1,
            )
            return None
        if is_answer_unsafe_statement_text(statement, **self._answer_safety_kwargs()):
            return None
        if graph_statement_non_theorem_reason(statement):
            self.increment_tool_metric(
                "mini_proposed_helpers_rejected_non_theorem_statement",
                1,
            )
            return None
        admission_quality = verified_helper_admission_quality(statement)
        if not admission_quality.auxiliary_target_admissible:
            self.increment_tool_metric(
                "mini_proposed_helpers_rejected_structurally_vacuous",
                1,
            )
            return None
        if not graph_statement_is_executable(
            statement
        ) and not _graph_statement_is_context_bare_prop_atom(
            statement,
            root_statement=self.root_statement,
        ):
            self.increment_tool_metric(
                "mini_proposed_helpers_rejected_non_executable_statement",
                1,
            )
            return None
        statement_key = canonical_dossier_statement_key(statement)
        if statement_key == canonical_dossier_statement_key(self.root_statement):
            return None
        if self.invalidated_statement_reason(statement):
            return None
        existing = self.proposed_helpers.get(name)
        verified_equivalent = _verified_helper_for_statement_key(
            self,
            statement_key,
            verification_environment_hash=str(
                self.current_lean_environment_hash or ""
            ).strip(),
        )
        if verified_equivalent is not None:
            previous_statement_key = (
                canonical_dossier_statement_key(existing.statement)
                if existing is not None
                else ""
            )
            starting_revision = (
                int(getattr(existing, "proposal_revision", 1) or 1)
                + (0 if previous_statement_key == statement_key else 1)
                if existing is not None
                else 1
            )
            proposal_revision = _next_proposed_helper_revision(
                self,
                name=name,
                statement=statement,
                starting_revision=starting_revision,
            )
            self.proposed_helpers.pop(name, None)
            if self.proof_graph is not None:
                ready_before = self._ready_route_ids()
                verified_node_id = self.proof_graph.helper_name_to_node_id.get(
                    verified_equivalent.name,
                    "",
                )
                _record_or_reuse_proposed_helper_graph_nodes(
                    self,
                    name=name,
                    statement=statement,
                    source=src,
                    phase=phase,
                    turn_index=turn_index,
                    proposal_revision=proposal_revision,
                )
                _resolve_graph_native_claims_for_statement_key(
                    self,
                    statement_key=statement_key,
                    verified_helper_name=verified_equivalent.name,
                    verified_node_id=verified_node_id,
                    source_hash=verified_equivalent.source_hash,
                    proof_hash=verified_equivalent.source_hash,
                    support_names=list(verified_equivalent.support_names),
                )
                _supersede_graph_native_proposals_for_helper_name(
                    self,
                    name,
                    verified_statement_key=statement_key,
                    superseded_statement_keys=(previous_statement_key,),
                    verified_node_id=verified_node_id,
                )
                self.reconcile_verified_facts(
                    trigger="proposed_helper_verified_equivalent",
                    ready_before=ready_before,
                    causal_helper_name=verified_equivalent.name,
                )
            return None
        if existing is not None:
            previous_statement_key = canonical_dossier_statement_key(existing.statement)
            starting_revision = int(getattr(existing, "proposal_revision", 1) or 1)
            if previous_statement_key != statement_key:
                starting_revision += 1
            proposal_revision = _next_proposed_helper_revision(
                self,
                name=name,
                statement=statement,
                starting_revision=starting_revision,
            )
            existing.source = src
            existing.source_hash = text_hash(src)
            existing.statement = statement
            existing.phase = str(phase or "")
            existing.turn_index = int(turn_index or 0)
            existing.proposal_revision = proposal_revision
            existing.statement_environment_hash = str(
                self.current_lean_environment_hash or ""
            ).strip()
            if self.proof_graph is not None:
                claim, _variant = _record_or_reuse_proposed_helper_graph_nodes(
                    self,
                    name=name,
                    statement=statement,
                    source=src,
                    phase=phase,
                    turn_index=turn_index,
                    proposal_revision=proposal_revision,
                )
                _supersede_stale_graph_native_proposals_for_helper_name(
                    self,
                    name,
                    active_statement_key=statement_key,
                    superseded_statement_keys=(previous_statement_key,),
                    superseding_node_id=claim.node_id if claim is not None else "",
                )
            return existing
        proposal_revision = _next_proposed_helper_revision(
            self,
            name=name,
            statement=statement,
            starting_revision=1,
        )
        proposed = ProposedHelper(
            name=name,
            statement=statement,
            source=src,
            source_hash=text_hash(src),
            phase=str(phase or ""),
            turn_index=int(turn_index or 0),
            proposal_revision=proposal_revision,
            statement_environment_hash=str(
                self.current_lean_environment_hash or ""
            ).strip(),
        )
        self.proposed_helpers[name] = proposed
        if self.proof_graph is not None:
            claim, _variant = _record_or_reuse_proposed_helper_graph_nodes(
                self,
                name=name,
                statement=statement,
                source=src,
                phase=phase,
                turn_index=turn_index,
                proposal_revision=proposal_revision,
            )
            _supersede_stale_graph_native_proposals_for_helper_name(
                self,
                name,
                active_statement_key=statement_key,
                superseding_node_id=claim.node_id if claim is not None else "",
            )
        return proposed

    def remove_verified_helper(self, name: str) -> bool:
        helper_name = str(name or "").strip()
        if not helper_name:
            return False
        removed = self.verified_helpers.pop(helper_name, None)
        if removed is None:
            return False
        self.verified_helper_eviction_generation += 1
        for helper in self.verified_helpers.values():
            helper.support_names = [
                support for support in helper.support_names if support != helper_name
            ]
            # Replay context is certificate provenance, not a live logical
            # edge. Preserve its name/hash tombstone so integrity and
            # renderability checks reject a dependent whose compilation
            # environment has been removed.
        # Fix 1 follow-up (2026-05-22): clean up alias map entries that
        # reference the removed helper. Code-reviewer adversarial finding
        # 3 flagged that ``resolve_verified_helper_name(alias)`` would
        # return a name no longer in ``verified_helpers`` after this
        # method ran — a dangling-reference analogue.
        # Drop alias entries whose canonical target is being removed.
        stale_aliases = [
            req
            for req, canonical in self.verified_helper_statement_aliases.items()
            if canonical == helper_name
        ]
        for req in stale_aliases:
            self.verified_helper_statement_aliases.pop(req, None)
        # Also drop the entry if `helper_name` itself was an alias key.
        self.verified_helper_statement_aliases.pop(helper_name, None)
        self.verified_helper_progress_deltas.pop(helper_name, None)
        if self.proof_graph is not None:
            self.proof_graph.remove_helper(helper_name)
            self._sync_legacy_helpers_to_graph()
        else:
            self._rebuild_semantic_fact_registry()
        # Reconciliation rebinds any graph targets to a surviving equivalent
        # attestation and ensures the removed helper cannot remain the live
        # certification source for the proposition.
        self.reconcile_verified_facts(trigger="verified_helper_removed")
        return True

    def _imported_helper_receipts_match_destination(
        self,
        helper: VerifiedHelper,
        *,
        helper_name: str,
        source: str,
        destination_helpers: Optional[Mapping[str, VerifiedHelper]] = None,
    ) -> bool:
        """Validate imported dependency receipts before recording anything.

        A verified helper's support hashes describe the exact declarations
        that were present when Lean checked it.  Recomputing those hashes from
        the destination would turn stale or missing evidence into a fresh
        receipt.  Imports therefore require a complete, exact match against
        the destination for logical support and replay-only context alike.
        """

        def ordered_names(values: Iterable[Any]) -> List[str]:
            names: List[str] = []
            for raw_name in list(values or []):
                name = str(raw_name or "").strip()
                if name and name != helper_name and name not in names:
                    names.append(name)
            return names

        support_names = ordered_names(
            getattr(helper, "support_names", []) or []
        )
        for inferred_name in self._canonical_support_names(
            self._referenced_verified_helper_names(
                source,
                skip=helper_name,
            )
        ):
            if inferred_name not in support_names:
                support_names.append(inferred_name)
        replay_context_names = ordered_names(
            getattr(helper, "replay_context_names", []) or []
        )

        def normalized_receipts(
            raw_receipts: Any,
        ) -> Optional[Dict[str, str]]:
            if not isinstance(raw_receipts, Mapping):
                return None
            receipts: Dict[str, str] = {}
            for raw_name, raw_hash in raw_receipts.items():
                name = str(raw_name or "").strip()
                source_hash = str(raw_hash or "").strip()
                if (
                    not name
                    or name == helper_name
                    or not source_hash
                    or name in receipts
                ):
                    return None
                receipts[name] = source_hash
            return receipts

        support_receipts = normalized_receipts(
            getattr(helper, "support_source_hashes", {}) or {}
        )
        replay_receipts = normalized_receipts(
            getattr(helper, "replay_context_source_hashes", {}) or {}
        )

        def receipts_match(
            names: Sequence[str],
            receipts: Optional[Dict[str, str]],
            *,
            metric_key: str,
        ) -> bool:
            if receipts is None or set(receipts) != set(names):
                self.increment_tool_metric(metric_key, 1)
                return False
            for dependency_name, recorded_hash in receipts.items():
                helper_registry = (
                    self.verified_helpers
                    if destination_helpers is None
                    else destination_helpers
                )
                destination_name = self._equivalent_helper_registry_name(
                    helper_registry,
                    dependency_name,
                )
                destination_helper = helper_registry.get(destination_name)
                destination_hash = str(
                    getattr(destination_helper, "source_hash", "") or ""
                ).strip()
                if not destination_hash or destination_hash != recorded_hash:
                    self.increment_tool_metric(metric_key, 1)
                    return False
            return True

        if not receipts_match(
            support_names,
            support_receipts,
            metric_key="mini_verified_helper_import_support_receipt_rejected",
        ):
            return False
        return receipts_match(
            replay_context_names,
            replay_receipts,
            metric_key="mini_verified_helper_import_replay_receipt_rejected",
        )

    def preflight_imported_verified_helper(
        self,
        helper: VerifiedHelper,
        *,
        destination_helpers: Optional[Mapping[str, VerifiedHelper]] = None,
    ) -> Optional[Dict[str, Any]]:
        """Validate an imported certificate without mutating dossier state."""

        source = str(getattr(helper, "source", "") or "").strip()
        helper_name = str(getattr(helper, "name", "") or "").strip()
        declared_name = str(helper_decl_name(source) or "").strip()
        recorded_source_hash = str(
            getattr(helper, "source_hash", "") or ""
        ).strip()
        if (
            not source
            or not helper_name
            or declared_name != helper_name
            or text_hash(source) != recorded_source_hash
        ):
            self.increment_tool_metric(
                "mini_verified_helper_import_source_identity_rejected",
                1,
            )
            return None
        incoming_statement = helper_decl_statement(source)
        if (
            not incoming_statement
            or graph_statement_non_theorem_reason(incoming_statement)
            or is_answer_unsafe_helper_source(
                source,
                **self._answer_safety_kwargs(),
            )
            or is_answer_unsafe_statement_text(
                incoming_statement,
                **self._answer_safety_kwargs(),
            )
        ):
            self.increment_tool_metric(
                "mini_verified_helper_import_source_policy_rejected",
                1,
            )
            return None
        evidence_environment_hash = str(
            getattr(helper, "verification_environment_hash", "") or ""
        ).strip()
        destination_environment_hash = str(
            self.current_lean_environment_hash or ""
        ).strip()
        compatible = (
            self.lean_environment_is_compatible(
                evidence_environment_hash,
                destination_environment_hash,
            )
            if destination_environment_hash
            else not evidence_environment_hash
        )
        if not compatible:
            self.increment_tool_metric(
                "mini_verified_helper_import_environment_rejected",
                1,
            )
            return None
        if not self._imported_helper_receipts_match_destination(
            helper,
            helper_name=helper_name,
            source=source,
            destination_helpers=destination_helpers,
        ):
            return None
        root_authority_tags = {
            "root_authoritative_helper",
            "root_exact_certificate",
            "root_finalization_certificate",
        }
        provenance_tags = [
            tag
            for tag in (
                str(raw_tag or "").strip()
                for raw_tag in list(
                    getattr(helper, "provenance_tags", []) or []
                )
            )
            if tag and tag not in root_authority_tags
        ]
        incoming_visibility = str(
            getattr(helper, "visibility_policy", "") or ""
        ).strip()
        import_visibility = (
            "" if incoming_visibility == "root_authoritative" else incoming_visibility
        )
        helper_registry = (
            self.verified_helpers
            if destination_helpers is None
            else destination_helpers
        )
        existing_helper_name = (
            self._equivalent_helper_registry_name(helper_registry, helper_name)
            or helper_name
        )
        existing = helper_registry.get(existing_helper_name)
        existing_hash = str(getattr(existing, "source_hash", "") or "").strip()
        incoming_identity = verified_helper_bound_contract_identity(helper)
        existing_identity = verified_helper_bound_contract_identity(existing)
        if (
            existing is not None
            and existing_hash != recorded_source_hash
            and not verified_helper_surface_statement_changed(existing, helper)
            and existing_identity
            and incoming_identity
            and verified_helper_semantic_statement_changed(existing, helper)
        ):
            self.increment_tool_metric(
                "mini_verified_helper_import_replacement_contract_conflict",
                1,
            )
            return None
        if (
            existing is not None
            and existing_hash == recorded_source_hash
            and not self._imported_same_source_evidence_is_compatible(
                existing,
                helper,
                incoming_visibility_policy=import_visibility,
            )
        ):
            return None
        stale_dependents: Set[str] = set()
        if existing is not None and existing_hash != recorded_source_hash:
            replacement_dependents: Set[str] = set()
            blockers = {existing_helper_name}
            progressed = True
            while progressed:
                progressed = False
                for dependent_name, dependent in helper_registry.items():
                    if (
                        dependent_name in blockers
                        or dependent_name in replacement_dependents
                    ):
                        continue
                    dependency_names = {
                        str(name or "").strip()
                        for name in (
                            *list(getattr(dependent, "support_names", []) or []),
                            *list(
                                getattr(dependent, "replay_context_names", []) or []
                            ),
                            *list(
                                dict(
                                    getattr(
                                        dependent,
                                        "support_source_hashes",
                                        {},
                                    )
                                    or {}
                                )
                            ),
                            *list(
                                dict(
                                    getattr(
                                        dependent,
                                        "replay_context_source_hashes",
                                        {},
                                    )
                                    or {}
                                )
                            ),
                            *self._referenced_verified_helper_names(
                                dependent.source,
                                skip=dependent_name,
                            ),
                        )
                        if str(name or "").strip()
                    }
                    if dependency_names & (blockers | replacement_dependents):
                        replacement_dependents.add(dependent_name)
                        progressed = True
            incoming_dependencies = {
                str(name or "").strip()
                for name in (
                    *list(getattr(helper, "support_names", []) or []),
                    *list(getattr(helper, "replay_context_names", []) or []),
                    *self._referenced_verified_helper_names(
                        source,
                        skip=helper_name,
                    ),
                )
                if str(name or "").strip()
            }
            if incoming_dependencies & replacement_dependents:
                self.increment_tool_metric(
                    "mini_verified_helper_import_replacement_cycle_rejected",
                    1,
                )
                return None
            if verified_helper_semantic_statement_changed(existing, helper):
                stale_dependents = replacement_dependents
        return {
            "source": source,
            "helper_name": helper_name,
            "existing_helper_name": existing_helper_name,
            "evidence_environment_hash": evidence_environment_hash,
            "contract_identity": verified_helper_bound_contract_identity(helper),
            "provenance_tags": provenance_tags,
            "incoming_visibility": incoming_visibility,
            "import_visibility": import_visibility,
            "stale_dependents": sorted(stale_dependents),
            "authority_downgraded": bool(
                len(provenance_tags)
                != len(
                    [
                        tag
                        for tag in list(
                            getattr(helper, "provenance_tags", []) or []
                        )
                        if str(tag or "").strip()
                    ]
                )
                or import_visibility != incoming_visibility
            ),
        }

    def record_imported_verified_helper(
        self,
        helper: VerifiedHelper,
        *,
        phase: Optional[str] = None,
        turn_index: Optional[int] = None,
    ) -> Optional[VerifiedHelper]:
        """Import one checked helper without laundering its Lean evidence.

        Child/branch transfers must preserve the environment in which Lean
        checked the declaration and its structural statement identity.  The
        destination may consume ancestor evidence after a recorded monotone
        extension, but a descendant or unstamped receipt is not silently
        restamped as destination-verified.

        Destination-owned quality/open-premise fields are deliberately
        recomputed by ``record_verified_helper``.  Provenance, visibility
        policy, dependency receipts, and valid Lean contract evidence survive
        the transfer.
        """

        preflight = self.preflight_imported_verified_helper(helper)
        if preflight is None:
            return None
        source = str(preflight["source"])
        helper_name = str(preflight["helper_name"])
        existing_helper_name = str(
            preflight.get("existing_helper_name") or helper_name
        )
        evidence_environment_hash = str(
            preflight["evidence_environment_hash"]
        )
        contract_identity = str(preflight["contract_identity"])
        provenance_tags = list(preflight["provenance_tags"])
        import_visibility = str(preflight["import_visibility"])
        if bool(preflight["authority_downgraded"]):
            self.increment_tool_metric(
                "mini_verified_helper_import_root_authority_downgraded",
                1,
            )
        existing = self.verified_helpers.get(existing_helper_name)
        if (
            existing is not None
            and str(existing.source_hash or "").strip()
            == str(getattr(helper, "source_hash", "") or "").strip()
        ):
            if not self._imported_same_source_evidence_is_compatible(
                existing,
                helper,
                incoming_visibility_policy=import_visibility,
            ):
                return None
            self._refresh_imported_verified_helper_evidence_preflighted(
                helper_name,
                helper,
            )
            return existing
        stale_dependents = {
            str(name or "").strip()
            for name in list(preflight.get("stale_dependents") or [])
            if str(name or "").strip()
        }
        recorded = self.record_verified_helper(
            source,
            phase=(
                str(phase)
                if phase is not None
                else str(getattr(helper, "phase", "") or "")
            ),
            turn_index=(
                int(turn_index or 0)
                if turn_index is not None
                else int(getattr(helper, "turn_index", 0) or 0)
            ),
            support_names=[
                str(name or "").strip()
                for name in list(getattr(helper, "support_names", []) or [])
                if str(name or "").strip()
                and str(name or "").strip() != helper_name
            ],
            replay_context_names=[
                str(name or "").strip()
                for name in list(
                    getattr(helper, "replay_context_names", []) or []
                )
                if str(name or "").strip()
                and str(name or "").strip() != helper_name
            ],
            provenance_tags=provenance_tags,
            visibility_policy=import_visibility,
            contract_identity=contract_identity,
            contract_display_statement=(
                str(getattr(helper, "contract_display_statement", "") or "")
                if contract_identity
                else ""
            ),
            contract_binder_sorts=(
                list(getattr(helper, "contract_binder_sorts", []) or [])
                if contract_identity
                else ()
            ),
            contract_proof_binder_types=(
                list(
                    getattr(
                        helper,
                        "contract_proof_binder_types",
                        [],
                    )
                    or []
                )
                if contract_identity
                else ()
            ),
            _contract_identity_statement=(
                helper_decl_statement(source) if contract_identity else ""
            ),
            _verification_environment_hash=evidence_environment_hash,
        )
        if recorded is None:
            return None
        landed_replaced_existing = bool(
            canonical_lean_identifier(str(getattr(recorded, "name", "") or ""))
            == canonical_lean_identifier(existing_helper_name)
            and str(getattr(recorded, "source_hash", "") or "").strip()
            == str(getattr(helper, "source_hash", "") or "").strip()
        )
        if landed_replaced_existing:
            for dependent_name in sorted(stale_dependents):
                self.remove_verified_helper(dependent_name)
        if stale_dependents and landed_replaced_existing:
            self.increment_tool_metric(
                "mini_verified_helper_import_stale_dependents_removed",
                len(stale_dependents),
            )
        return recorded

    def _imported_same_source_evidence_is_compatible(
        self,
        existing: VerifiedHelper,
        incoming: VerifiedHelper,
        *,
        incoming_visibility_policy: Optional[str] = None,
    ) -> bool:
        """Preflight non-receipt evidence for a byte-identical import."""

        existing_environment = str(
            existing.verification_environment_hash or ""
        ).strip()
        incoming_environment = str(
            getattr(incoming, "verification_environment_hash", "") or ""
        ).strip()
        if existing_environment != incoming_environment:
            return False
        existing_identity = verified_helper_bound_contract_identity(existing)
        incoming_identity = verified_helper_bound_contract_identity(incoming)
        existing_identity_valid = has_lean_contract_identity(existing_identity)
        incoming_identity_valid = has_lean_contract_identity(incoming_identity)
        if (
            existing_identity_valid
            and incoming_identity_valid
            and existing_identity != incoming_identity
        ):
            self.increment_tool_metric(
                "mini_verified_helper_import_contract_conflict",
                1,
            )
            return False
        if (
            existing_identity_valid
            and incoming_identity_valid
            and existing_identity == incoming_identity
        ):
            existing_display = str(
                existing.contract_display_statement or ""
            ).strip()
            incoming_display = str(
                getattr(incoming, "contract_display_statement", "") or ""
            ).strip()
            if (
                existing_display
                and incoming_display
                and existing_display != incoming_display
            ):
                self.increment_tool_metric(
                    "mini_verified_helper_import_contract_metadata_conflict",
                    1,
                )
                return False
            for field_name in (
                "contract_binder_sorts",
                "contract_proof_binder_types",
            ):
                existing_values = [
                    str(value or "")
                    for value in list(getattr(existing, field_name, []) or [])
                    if str(value or "").strip()
                ]
                incoming_values = [
                    str(value or "")
                    for value in list(getattr(incoming, field_name, []) or [])
                    if str(value or "").strip()
                ]
                if (
                    existing_values
                    and incoming_values
                    and existing_values != incoming_values
                ):
                    self.increment_tool_metric(
                        "mini_verified_helper_import_contract_metadata_conflict",
                        1,
                    )
                    return False
        incoming_visibility = str(
            (
                getattr(incoming, "visibility_policy", "")
                if incoming_visibility_policy is None
                else incoming_visibility_policy
            )
            or ""
        ).strip()
        existing_visibility = str(existing.visibility_policy or "").strip()
        if existing_visibility != incoming_visibility:
            self.increment_tool_metric(
                "mini_verified_helper_import_visibility_conflict",
                1,
            )
            return False
        return True

    def refresh_imported_verified_helper_evidence(
        self,
        name: str,
        incoming: VerifiedHelper,
    ) -> bool:
        """Safely refresh a same-source helper through the full import boundary."""

        helper_name = str(name or "").strip()
        existing = self.verified_helpers.get(helper_name)
        if existing is None or incoming is None:
            return False
        if str(getattr(incoming, "name", "") or "").strip() != helper_name:
            return False
        before = copy.deepcopy(existing)
        accepted = self.record_imported_verified_helper(incoming)
        return accepted is existing and existing != before

    def _refresh_imported_verified_helper_evidence_preflighted(
        self,
        name: str,
        incoming: VerifiedHelper,
    ) -> bool:
        """Monotonically enrich a byte-identical helper from a trusted import.

        Structural evidence is transferable only when both records were
        checked in the same environment.  Merely knowing that the incoming
        environment is an ancestor is sufficient to *use* its theorem, but
        not to claim that identical surface text elaborates to the same Expr
        in a descendant where notation or name resolution may have changed.
        Conflicting structural identities therefore fail closed. Dependency
        receipts are unioned monotonically: an incoming revalidation may add
        or correct a destination-matching receipt, but cannot erase an older
        receipt. A stale unmentioned receipt remains a conservative tombstone
        until an explicit revalidation/removal path adjudicates it.
        """

        helper_name = str(name or "").strip()
        existing = self.verified_helpers.get(helper_name)
        if existing is None or incoming is None:
            return False
        if str(existing.source_hash or "").strip() != str(
            getattr(incoming, "source_hash", "") or ""
        ).strip():
            return False
        existing_identity = verified_helper_bound_contract_identity(existing)
        incoming_identity = verified_helper_bound_contract_identity(incoming)
        existing_identity_valid = has_lean_contract_identity(existing_identity)
        incoming_identity_valid = has_lean_contract_identity(incoming_identity)

        incoming_display = str(
            getattr(incoming, "contract_display_statement", "") or ""
        ).strip()
        existing_display = str(
            existing.contract_display_statement or ""
        ).strip()
        incoming_contract_lists: Dict[str, List[str]] = {}
        for field_name in (
            "contract_binder_sorts",
            "contract_proof_binder_types",
        ):
            incoming_values = [
                str(value or "")
                for value in list(
                    getattr(incoming, field_name, []) or []
                )
                if str(value or "").strip()
            ]
            incoming_contract_lists[field_name] = incoming_values

        incoming_support_names: List[str] = []
        for raw_name in list(getattr(incoming, "support_names", []) or []):
            support_name = str(raw_name or "").strip()
            if (
                support_name
                and support_name != helper_name
                and support_name not in incoming_support_names
            ):
                incoming_support_names.append(support_name)
        incoming_support_hashes = {
            str(support_name or "").strip(): str(source_hash or "").strip()
            for support_name, source_hash in dict(
                getattr(incoming, "support_source_hashes", {}) or {}
            ).items()
            if str(support_name or "").strip()
            and str(support_name or "").strip() != helper_name
            and str(source_hash or "").strip()
        }
        for support_name in incoming_support_hashes:
            if support_name not in incoming_support_names:
                incoming_support_names.append(support_name)
        merged_support_names = [
            str(support_name or "").strip()
            for support_name in list(existing.support_names or [])
            if str(support_name or "").strip()
            and str(support_name or "").strip() != helper_name
        ]
        for support_name in incoming_support_names:
            if support_name not in merged_support_names:
                merged_support_names.append(support_name)
        merged_support_hashes = {
            str(support_name or "").strip(): str(source_hash or "").strip()
            for support_name, source_hash in dict(
                existing.support_source_hashes or {}
            ).items()
            if str(support_name or "").strip()
            and str(support_name or "").strip() != helper_name
            and str(source_hash or "").strip()
        }
        merged_support_hashes.update(incoming_support_hashes)

        incoming_replay_names: List[str] = []
        for raw_name in list(
            getattr(incoming, "replay_context_names", []) or []
        ):
            replay_name = str(raw_name or "").strip()
            if (
                replay_name
                and replay_name != helper_name
                and replay_name not in incoming_replay_names
            ):
                incoming_replay_names.append(replay_name)
        incoming_replay_hashes = {
            str(replay_name or "").strip(): str(source_hash or "").strip()
            for replay_name, source_hash in dict(
                getattr(incoming, "replay_context_source_hashes", {}) or {}
            ).items()
            if str(replay_name or "").strip()
            and str(replay_name or "").strip() != helper_name
            and str(source_hash or "").strip()
        }
        for replay_name in incoming_replay_hashes:
            if replay_name not in incoming_replay_names:
                incoming_replay_names.append(replay_name)
        merged_replay_names = [
            str(replay_name or "").strip()
            for replay_name in list(existing.replay_context_names or [])
            if str(replay_name or "").strip()
            and str(replay_name or "").strip() != helper_name
        ]
        for replay_name in incoming_replay_names:
            if replay_name not in merged_replay_names:
                merged_replay_names.append(replay_name)
        merged_replay_hashes = {
            str(replay_name or "").strip(): str(source_hash or "").strip()
            for replay_name, source_hash in dict(
                existing.replay_context_source_hashes or {}
            ).items()
            if str(replay_name or "").strip()
            and str(replay_name or "").strip() != helper_name
            and str(source_hash or "").strip()
        }
        merged_replay_hashes.update(incoming_replay_hashes)

        changed = False
        if list(existing.support_names or []) != merged_support_names:
            existing.support_names = merged_support_names
            changed = True
        if dict(existing.support_source_hashes or {}) != merged_support_hashes:
            existing.support_source_hashes = merged_support_hashes
            changed = True
        if list(existing.replay_context_names or []) != merged_replay_names:
            existing.replay_context_names = merged_replay_names
            changed = True
        if (
            dict(existing.replay_context_source_hashes or {})
            != merged_replay_hashes
        ):
            existing.replay_context_source_hashes = merged_replay_hashes
            changed = True
        identity_upgraded = (
            not existing_identity_valid and incoming_identity_valid
        )
        if identity_upgraded:
            existing.contract_identity = incoming_identity
            existing.contract_identity_statement_key = str(
                getattr(incoming, "contract_identity_statement_key", "") or ""
            ).strip()
            existing.contract_identity_environment_hash = str(
                getattr(incoming, "contract_identity_environment_hash", "") or ""
            ).strip()
            existing.contract_identity_evidence_receipt = str(
                getattr(incoming, "contract_identity_evidence_receipt", "") or ""
            ).strip()
            changed = True
            if existing.contract_display_statement != incoming_display:
                existing.contract_display_statement = incoming_display
                changed = True
            for field_name, incoming_values in incoming_contract_lists.items():
                if list(getattr(existing, field_name, []) or []) != incoming_values:
                    setattr(existing, field_name, incoming_values)
                    changed = True
        elif (
            incoming_identity_valid
            and verified_helper_bound_contract_identity(existing)
            == incoming_identity
        ):
            if incoming_display and not existing_display:
                existing.contract_display_statement = incoming_display
                changed = True
            for field_name, incoming_values in incoming_contract_lists.items():
                if incoming_values and not list(
                    getattr(existing, field_name, []) or []
                ):
                    setattr(existing, field_name, incoming_values)
                    changed = True

        existing_tags = [
            str(tag or "").strip()
            for tag in list(existing.provenance_tags or [])
            if str(tag or "").strip()
        ]
        authoritative_tags = {
            "root_authoritative_helper",
            "root_exact_certificate",
            "root_finalization_certificate",
        }
        for raw_tag in list(
            getattr(incoming, "provenance_tags", []) or []
        ):
            tag = str(raw_tag or "").strip()
            if (
                tag
                and tag not in authoritative_tags
                and tag not in existing_tags
            ):
                existing_tags.append(tag)
                changed = True
        if changed:
            existing.provenance_tags = existing_tags
        if not changed:
            return False

        self._classify_verified_helper_quality(existing)
        self._refresh_verified_helper_statement_aliases(record_metric=True)
        graph = self.proof_graph
        if graph is not None:
            node_id = str(
                graph.helper_name_to_node_id.get(helper_name) or ""
            ).strip()
            node = graph.nodes.get(node_id)
            if node is not None:
                graph.mark_node_proved(
                    node_id,
                    source_hash=str(existing.source_hash or ""),
                    proof_hash=str(existing.source_hash or ""),
                    support_names=existing.support_names,
                )
                node.metadata.update(
                    {
                        "verified_helper_provenance_tags": list(
                            existing.provenance_tags
                        ),
                        "verified_helper_visibility_policy": (
                            existing.visibility_policy
                        ),
                        "verified_helper_quality_tags": list(
                            existing.quality_tags
                        ),
                        "verified_helper_render_policy": existing.render_policy,
                        **self._verified_helper_answer_safety_metadata(existing),
                        "verified_helper_open_premise_statement_keys": list(
                            existing.open_premise_statement_keys
                        ),
                        "verified_helper_open_premise_statements": list(
                            existing.closed_open_premise_statements
                        ),
                        "verified_helper_contract_identity": (
                            verified_helper_bound_contract_identity(existing)
                        ),
                        "verified_helper_contract_identity_statement_key": str(
                            existing.contract_identity_statement_key or ""
                        ),
                        "verified_helper_contract_identity_environment_hash": str(
                            existing.contract_identity_environment_hash or ""
                        ),
                        "verified_helper_contract_identity_evidence_receipt": str(
                            existing.contract_identity_evidence_receipt or ""
                        ),
                        "verified_helper_contract_display_statement": (
                            existing.contract_display_statement
                        ),
                        "verified_helper_contract_binder_sorts": list(
                            existing.contract_binder_sorts
                        ),
                        "verified_helper_contract_proof_binder_types": list(
                            existing.contract_proof_binder_types
                        ),
                    }
                )
        self.reconcile_verified_facts(
            trigger="verified_helper_import_evidence_refresh",
        )
        return True

    def record_verified_helper(
        self,
        source: str,
        *,
        phase: str,
        turn_index: int,
        support_names: Optional[Iterable[str]] = None,
        replay_context_names: Optional[Iterable[str]] = None,
        provenance_tags: Optional[Iterable[str]] = None,
        visibility_policy: str = "",
        contract_identity: str = "",
        contract_display_statement: str = "",
        contract_binder_sorts: Optional[Iterable[str]] = None,
        contract_proof_binder_types: Optional[Iterable[str]] = None,
        _contract_identity_statement: str = "",
        _verification_environment_hash: Optional[str] = None,
        replace_existing_same_name: bool = False,
        _defer_global_derived_refresh: bool = False,
    ) -> Optional[VerifiedHelper]:
        declared_name = helper_decl_name(source)
        if not declared_name:
            return None
        name = (
            self._equivalent_helper_registry_name(
                self.verified_helpers,
                declared_name,
            )
            or declared_name
        )
        src = str(source or "").strip()
        if not src:
            return None
        ready_route_ids_before_accept = self._ready_route_ids()
        if is_answer_unsafe_helper_source(src, **self._answer_safety_kwargs()):
            return None
        # Fix 1 (2026-05-22): canonical-statement dedup (soft).
        # If another verified helper already exists under a DIFFERENT name
        # with the same canonical statement, record an alias so downstream
        # consumers can collapse them. Both helpers remain stored.
        incoming_statement = helper_decl_statement(src)
        if not incoming_statement:
            self.increment_tool_metric(
                "mini_verified_helpers_rejected_malformed_statement",
                1,
            )
            return None
        equivalent_existing = self.verified_helpers.get(name)
        if (
            equivalent_existing is not None
            and declared_name != name
            and canonical_dossier_statement_key(
                helper_decl_statement(
                    str(getattr(equivalent_existing, "source", "") or "")
                )
            )
            == canonical_dossier_statement_key(incoming_statement)
        ):
            return equivalent_existing
        if is_answer_unsafe_statement_text(
            incoming_statement,
            **self._answer_safety_kwargs(),
        ):
            return None
        non_theorem_reason = graph_statement_non_theorem_reason(incoming_statement)
        if non_theorem_reason:
            self.increment_tool_metric(
                "mini_verified_helpers_rejected_non_theorem_statement",
                1,
            )
            return None
        incoming_statement_key = canonical_dossier_statement_key(incoming_statement)
        support_name_list: List[str] = []
        for raw_name in list(support_names or []):
            clean = str(raw_name or "").strip()
            if clean and clean != name and clean not in support_name_list:
                support_name_list.append(clean)
        for inferred_name in self._canonical_support_names(
            self._referenced_verified_helper_names(src, skip=name)
        ):
            if inferred_name not in support_name_list:
                support_name_list.append(inferred_name)
        support_source_hashes: Dict[str, str] = {}
        for support_name in support_name_list:
            support_key = str(support_name or "").strip()
            if not support_key or support_key == name:
                continue
            support = self.verified_helpers.get(support_key)
            support_hash = str(getattr(support, "source_hash", "") or "").strip()
            if support_hash:
                support_source_hashes[support_key] = support_hash
        replay_context_name_list: List[str] = []
        for raw_name in list(replay_context_names or []):
            clean = str(raw_name or "").strip()
            if clean and clean != name and clean not in replay_context_name_list:
                replay_context_name_list.append(clean)
        replay_context_source_hashes: Dict[str, str] = {}
        for replay_name in replay_context_name_list:
            replay_helper = self.verified_helpers.get(replay_name)
            replay_hash = str(
                getattr(replay_helper, "source_hash", "") or ""
            ).strip()
            if replay_hash:
                replay_context_source_hashes[replay_name] = replay_hash
        verification_environment_hash = str(
            (
                self.current_lean_environment_hash
                if _verification_environment_hash is None
                else _verification_environment_hash
            )
            or ""
        )
        incoming_contract_identity = str(contract_identity or "").strip()
        evidence_statement_key = canonical_dossier_statement_key(
            _contract_identity_statement
        )
        contract_evidence_valid = bool(
            has_lean_contract_identity(incoming_contract_identity)
            and evidence_statement_key
            and evidence_statement_key == incoming_statement_key
        )
        if incoming_contract_identity and not contract_evidence_valid:
            self.increment_tool_metric(
                "mini_verified_helper_contract_evidence_rejected",
                1,
            )
        bound_contract_identity = (
            incoming_contract_identity if contract_evidence_valid else ""
        )
        contract_evidence_receipt = (
            make_lean_contract_evidence_receipt(
                bound_contract_identity,
                evidence_statement_key,
                verification_environment_hash,
            )
            if bound_contract_identity
            else ""
        )
        item = VerifiedHelper(
            name=name,
            source=src,
            source_hash=text_hash(src),
            phase=str(phase or ""),
            turn_index=int(turn_index or 0),
            support_names=support_name_list,
            support_source_hashes=support_source_hashes,
            replay_context_names=replay_context_name_list,
            replay_context_source_hashes=replay_context_source_hashes,
            provenance_tags=[
                str(tag or "").strip()
                for tag in list(provenance_tags or [])
                if str(tag or "").strip()
            ],
            visibility_policy=str(visibility_policy or "").strip(),
            verification_environment_hash=verification_environment_hash,
            contract_identity=bound_contract_identity,
            contract_identity_statement_key=(
                evidence_statement_key if bound_contract_identity else ""
            ),
            contract_identity_environment_hash=(
                verification_environment_hash if bound_contract_identity else ""
            ),
            contract_identity_evidence_receipt=contract_evidence_receipt,
            contract_display_statement=str(
                contract_display_statement or ""
            ).strip(),
            contract_binder_sorts=[
                str(item or "")
                for item in list(contract_binder_sorts or [])
                if str(item or "").strip()
            ],
            contract_proof_binder_types=[
                str(item or "")
                for item in list(contract_proof_binder_types or [])
                if str(item or "").strip()
            ],
        )
        self._classify_verified_helper_quality(item)
        if str(getattr(item, "render_policy", "") or "") == "advisory_root_equivalent":
            self.increment_tool_metric(
                "mini_verified_root_equivalent_helpers_withheld",
                1,
            )
        if "hollow_root_reducer" in item.quality_tags:
            self.increment_tool_metric("mini_hollow_root_reducers_detected", 1)
        if "negative_evidence_helper" in item.quality_tags:
            self.increment_tool_metric("mini_negative_evidence_helpers_withheld", 1)
        existing = self.verified_helpers.get(name)
        if (
            existing is not None
            and not verified_helper_surface_statement_changed(existing, item)
            and verified_helper_bound_contract_identity(existing)
            and not verified_helper_bound_contract_identity(item)
        ):
            self.increment_tool_metric(
                "mini_verified_helper_contract_authority_downgrade_rejected",
                1,
            )
            return None
        if (
            existing is not None
            and verified_helper_semantic_statement_changed(existing, item)
            and not replace_existing_same_name
        ):
            alternative_name = fresh_lean_alternative_identifier(
                name,
                tuple(
                    dict.fromkeys(
                        (
                            *self.verified_helpers,
                            *self.proposed_helpers,
                            *(
                                self.proof_graph.helper_name_to_node_id
                                if self.proof_graph is not None
                                else {}
                            ),
                        )
                    )
                ),
            )
            alternative_source = rename_lean_identifier(
                src,
                name,
                alternative_name,
            )
            self.increment_tool_metric(
                "mini_verified_helper_name_collisions_disambiguated",
                1,
            )
            return self.record_verified_helper(
                alternative_source,
                phase=phase,
                turn_index=turn_index,
                support_names=support_name_list,
                replay_context_names=replay_context_name_list,
                provenance_tags=list(item.provenance_tags),
                visibility_policy=visibility_policy,
                contract_identity=contract_identity,
                contract_display_statement=contract_display_statement,
                contract_binder_sorts=contract_binder_sorts,
                contract_proof_binder_types=contract_proof_binder_types,
                _contract_identity_statement=_contract_identity_statement,
                _verification_environment_hash=verification_environment_hash,
                _defer_global_derived_refresh=_defer_global_derived_refresh,
            )
        if (
            existing is not None
            and replace_existing_same_name
            and verified_helper_semantic_statement_changed(existing, item)
        ):
            # This mode is reserved for a declaration that participated under
            # this exact name in a freshly accepted whole-proof replay.  The
            # accepted proof is authority that the corrected declaration, not
            # the stale registry entry, owns the name.  Ordinary independent
            # collisions retain the disambiguating branch above.
            self.increment_tool_metric(
                "mini_verified_helper_same_name_corrections_replaced",
                1,
            )
        # Last write wins on ``name`` at the dict level. Note (Bonus #3
        # fix, 2026-05-08, after A8): the helper-salvage path now allows
        # (name, statement_signature) corrections to reach this assignment
        # — i.e. when the model emits a same-name helper with a DIFFERENT
        # statement that Lean accepts, the corrected version replaces the
        # stale entry here. Earlier comments claimed callers should avoid
        # conflicting redefinitions; that's no longer accurate, so the
        # write must remain unconditional and idempotent at the dict
        # level (proof_graph also reflects the new statement via
        # ``ensure_helper`` below).
        existing = self.verified_helpers.get(name)
        if existing is not None:
            old_hash = str(getattr(existing, "source_hash", "") or "").strip()
            new_hash = str(getattr(item, "source_hash", "") or "").strip()
            statement_changed = verified_helper_semantic_statement_changed(
                existing,
                item,
            )
            helper_hash_history = self.verified_helper_source_hash_history.setdefault(
                name,
                [],
            )
            if old_hash and new_hash and old_hash != new_hash and statement_changed:
                superseded = self.superseded_verified_helper_hashes.setdefault(
                    name, []
                )
                for stale_hash in [*helper_hash_history, old_hash]:
                    if stale_hash and stale_hash not in superseded:
                        superseded.append(stale_hash)
                helper_hash_history.clear()
            elif old_hash and new_hash and old_hash != new_hash:
                if old_hash not in helper_hash_history:
                    helper_hash_history.append(old_hash)
                # A same-statement replacement is a new Lean source identity.
                # Existing dependents retain the exact support/replay receipts
                # under which they were checked and therefore become stale.
                # Only the replacement pipeline, after replay-validating those
                # dependents, may call
                # ``refresh_revalidated_dependent_support_hashes`` to bind them
                # to ``new_hash``.  Rewriting receipts here would manufacture
                # validation evidence from registry mutation alone.
            # A corrected helper may gain dependencies that were introduced
            # later in the run. Move the replacement to the end of the stable
            # dict order so replay contexts do not retain the stale forward
            # reference shape from the old declaration.
            self.verified_helpers.pop(name, None)
        self.verified_helpers[name] = item
        if not _defer_global_derived_refresh:
            self._refresh_verified_helper_quality()
            self._refresh_verified_helper_statement_aliases(record_metric=True)
        prior_proposed = self.proposed_helpers.get(name)
        superseded_proposal_statement_keys = (
            (canonical_dossier_statement_key(prior_proposed.statement),)
            if prior_proposed is not None
            else ()
        )
        # A verified helper supersedes any prior proposal under the same
        # name — the planner should not see "still proposed" for a helper
        # the prover has already proved. (Banking-from-direct-author fix,
        # 2026-05-13: proposed_helpers seeds the planner; verified evicts.)
        self.proposed_helpers.pop(name, None)
        parent_progress_claim_ids: List[str] = []
        parent_progress_variant_ids: List[str] = []
        parent_progress_obligation_ids: List[str] = []
        statement_key = incoming_statement_key
        if self.proof_graph is not None:
            node = self.proof_graph.ensure_helper(
                name,
                statement=helper_decl_statement(src),
                phase=phase,
                turn_index=turn_index,
                support_names=support_name_list,
                metadata={
                    "verified_helper_source": src,
                    "verified_helper_source_hash": item.source_hash,
                    **self._verified_helper_answer_safety_metadata(item),
                    "verified_helper_provenance_tags": list(item.provenance_tags),
                    "verified_helper_visibility_policy": item.visibility_policy,
                    "verified_helper_quality_tags": list(item.quality_tags),
                    "verified_helper_render_policy": item.render_policy,
                    "verified_helper_open_premise_statement_keys": list(
                        item.open_premise_statement_keys
                    ),
                    "verified_helper_open_premise_statements": list(
                        item.closed_open_premise_statements
                    ),
                    "verified_helper_contract_identity": (
                        verified_helper_bound_contract_identity(item)
                    ),
                    "verified_helper_contract_identity_statement_key": str(
                        item.contract_identity_statement_key or ""
                    ),
                    "verified_helper_contract_identity_environment_hash": str(
                        item.contract_identity_environment_hash or ""
                    ),
                    "verified_helper_contract_identity_evidence_receipt": str(
                        item.contract_identity_evidence_receipt or ""
                    ),
                    "verified_helper_contract_display_statement": (
                        item.contract_display_statement
                    ),
                    "verified_helper_contract_binder_sorts": list(
                        item.contract_binder_sorts
                    ),
                    "verified_helper_contract_proof_binder_types": list(
                        item.contract_proof_binder_types
                    ),
                    "verified_helper_environment_hash": str(
                        item.verification_environment_hash or ""
                    ),
                },
            )
            reviver = getattr(self.proof_graph, "revive_verified_helper_node", None)
            if callable(reviver):
                try:
                    reviver(node.node_id)
                except Exception:
                    pass
            self.proof_graph.mark_node_proved(
                node.node_id,
                source_hash=item.source_hash,
                proof_hash=item.source_hash,
                support_names=support_name_list,
            )
            proved_node = self.proof_graph.nodes.get(node.node_id)
            if (
                proved_node is None
                or str(getattr(proved_node, "status", "") or "") != "proved"
                or str(getattr(proved_node, "source_hash", "") or "").strip()
                != str(item.source_hash or "").strip()
            ):
                self.increment_tool_metric(
                    "mini_verified_helper_graph_certification_failed",
                    1,
                )
                try:
                    self.record_attempt(
                        phase="verified_helper_graph_certification",
                        turn_index=int(turn_index or 0),
                        proof=src,
                        helper_names=[name],
                        verdict="verified_helper_graph_certification_failed",
                        error_type="graph_certification_failed",
                        node_id=node.node_id,
                        metadata={
                            "helper_name": name,
                            "expected_source_hash": item.source_hash,
                            "graph_node_status": str(
                                getattr(proved_node, "status", "") or ""
                            ),
                            "graph_node_source_hash": str(
                                getattr(proved_node, "source_hash", "") or ""
                            ),
                        },
                    )
                except Exception:
                    pass
            if self._verified_helper_context_visible(item):
                if verified_helper_admission_quality(item).generic_novelty:
                    _supersede_graph_native_proposals_for_helper_name(
                        self,
                        name,
                        verified_statement_key=statement_key,
                        superseded_statement_keys=(
                            superseded_proposal_statement_keys
                        ),
                        verified_node_id=node.node_id,
                    )
                _resolve_graph_native_claims_for_statement_key(
                    self,
                    statement_key=statement_key,
                    verified_helper_name=name,
                    verified_node_id=node.node_id,
                    source_hash=item.source_hash,
                    proof_hash=item.source_hash,
                    support_names=support_name_list,
                    resolved_claim_node_ids=parent_progress_claim_ids,
                    resolved_variant_node_ids=parent_progress_variant_ids,
                )
                _resolve_graph_native_obligations_for_statement_key(
                    self,
                    statement_key=statement_key,
                    verified_helper_name=name,
                    verified_node_id=node.node_id,
                    source_hash=item.source_hash,
                    proof_hash=item.source_hash,
                    support_names=support_name_list,
                    resolved_obligation_node_ids=parent_progress_obligation_ids,
                )
            else:
                exact_negative_certificates = 0
                exact_negative_candidates = 0
                if (
                    "negative_evidence_helper" not in item.quality_tags
                    and verified_helper_admission_quality(item).generic_novelty
                ):
                    _resolve_graph_native_obligations_for_statement_key(
                        self,
                        statement_key=statement_key,
                        verified_helper_name=name,
                        verified_node_id=node.node_id,
                        source_hash=item.source_hash,
                        proof_hash=item.source_hash,
                        support_names=support_name_list,
                        resolved_obligation_node_ids=parent_progress_obligation_ids,
                    )
                if "negative_evidence_helper" in item.quality_tags:
                    for candidate in list(self.proof_graph.nodes.values()):
                        if getattr(candidate, "kind", "") not in {
                            "proposed_claim",
                            "formal_variant",
                            "missing_obligation",
                        }:
                            continue
                        if bool((getattr(candidate, "metadata", {}) or {}).get("proposal_superseded")):
                            continue
                        if (
                            canonical_dossier_statement_key(
                                getattr(candidate, "statement", "") or ""
                            )
                            == statement_key
                        ):
                            exact_negative_candidates += 1
                    exact_negative_certificates += (
                        _resolve_graph_native_claims_for_statement_key(
                            self,
                            statement_key=statement_key,
                            verified_helper_name=name,
                            verified_node_id=node.node_id,
                            source_hash=item.source_hash,
                            proof_hash=item.source_hash,
                            support_names=support_name_list,
                            resolved_claim_node_ids=parent_progress_claim_ids,
                            resolved_variant_node_ids=parent_progress_variant_ids,
                        )
                    )
                    exact_negative_certificates += (
                        _resolve_graph_native_obligations_for_statement_key(
                            self,
                            statement_key=statement_key,
                            verified_helper_name=name,
                            verified_node_id=node.node_id,
                            source_hash=item.source_hash,
                            proof_hash=item.source_hash,
                            support_names=support_name_list,
                            resolved_obligation_node_ids=parent_progress_obligation_ids,
                        )
                    )
                    if exact_negative_certificates:
                        self.increment_tool_metric(
                            "mini_graph_negative_evidence_exact_certificates_accepted",
                            exact_negative_certificates,
                        )
                    negated_statement_key = _dossier_negated_statement_key(
                        helper_decl_statement(src)
                    )
                    contradicted_targets, contradicted_routes = (
                        _retire_graph_native_positive_targets_for_negative_evidence(
                            self,
                            negated_statement_key=negated_statement_key,
                            verified_helper_name=name,
                            verified_node_id=node.node_id,
                            statement=helper_decl_statement(src),
                            source_hash=item.source_hash,
                            evidence_environment_hash=str(
                                item.verification_environment_hash or ""
                            ).strip(),
                        )
                    )
                    if contradicted_targets:
                        self.increment_tool_metric(
                            "mini_graph_negative_evidence_contradicted_targets",
                            contradicted_targets,
                        )
                    if contradicted_routes:
                        self.increment_tool_metric(
                            "mini_graph_negative_evidence_contradicted_routes",
                            contradicted_routes,
                        )
                if "hollow_root_reducer" in item.quality_tags:
                    self.increment_tool_metric(
                        "mini_graph_hollow_reducer_certificates_blocked",
                        1,
                    )
                elif (
                    "negative_evidence_helper" in item.quality_tags
                    and exact_negative_candidates
                    and not exact_negative_certificates
                ):
                    self.increment_tool_metric(
                        "mini_graph_negative_evidence_certificates_blocked",
                        1,
                    )
            repair = getattr(
                self.proof_graph,
                "_repair_uncertified_graph_native_proved_nodes",
                None,
            )
            if callable(repair):
                repair()
        reconciliation = self.reconcile_verified_facts(
            trigger="verified_helper_accept",
            ready_before=ready_route_ids_before_accept,
            causal_helper_name=item.name,
        )
        reconciliation_progress_node_ids = (
            list(reconciliation.get("resolved_node_ids") or [])
            if verified_helper_admission_quality(item).generic_novelty
            else []
        )
        for node_id in reconciliation_progress_node_ids:
            node = (
                self.proof_graph.nodes.get(node_id)
                if self.proof_graph is not None
                else None
            )
            target = (
                parent_progress_claim_ids
                if getattr(node, "kind", "") == "proposed_claim"
                else parent_progress_variant_ids
                if getattr(node, "kind", "") == "formal_variant"
                else parent_progress_obligation_ids
            )
            if node_id not in target:
                target.append(node_id)
        canonical_helper_name = self.verified_helper_statement_aliases.get(name, name)
        theory_progress = bool(
            canonical_helper_name == name
            and _verified_helper_counts_for_theory_progress(self, item)
        )
        self.verified_helper_progress_deltas[name] = VerifiedHelperProgressDelta(
            helper_name=name,
            statement_key=statement_key,
            canonical_helper_name=canonical_helper_name,
            theory_progress=theory_progress,
            resolved_claim_node_ids=(
                list(parent_progress_claim_ids)
                if verified_helper_admission_quality(item).generic_novelty
                else []
            ),
            resolved_variant_node_ids=(
                list(parent_progress_variant_ids)
                if verified_helper_admission_quality(item).generic_novelty
                else []
            ),
            resolved_obligation_node_ids=(
                list(parent_progress_obligation_ids)
                if verified_helper_admission_quality(item).generic_novelty
                else []
            ),
        )
        self._refresh_verified_helper_progress_alias_fields()
        return item

    def record_attempt(
        self,
        *,
        phase: str,
        turn_index: int,
        proof: str,
        helper_names: Iterable[str] = (),
        verdict: str,
        error_type: str = "",
        node_id: Optional[str] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> None:
        helper_name_list = [name for name in helper_names if name]
        if self.proof_graph is not None:
            target = node_id or self.proof_graph.root_node_id
            self.proof_graph.record_attempt(
                target,
                phase=phase,
                turn_index=turn_index,
                proof=proof,
                helper_names=helper_name_list,
                verdict=verdict,
                error_type=error_type,
                metadata=metadata,
            )
        self.attempts.append(
            ProofAttemptRecord(
                phase=str(phase or ""),
                turn_index=int(turn_index or 0),
                proof_hash=text_hash(proof),
                helper_names=helper_name_list,
                verdict=str(verdict or ""),
                error_type=str(error_type or ""),
            )
        )
        self._compact_attempt_history()

    def _compact_attempt_history(self) -> int:
        """Bound duplicate dossier diagnostics while retaining a total count."""

        overflow = max(0, len(self.attempts) - _MAX_PROOF_ATTEMPT_RECORDS)
        if overflow <= 0:
            return 0
        del self.attempts[:overflow]
        metric = "proof_attempt_records_pruned"
        self.tool_metrics[metric] = int(self.tool_metrics.get(metric, 0) or 0) + overflow
        return overflow

    def record_scratch(
        self,
        *,
        turn_index: int,
        tool_call_index: int,
        ok: bool,
        summary: str,
        code: str,
        goal_statement: str = "",
        source_label: str = "try_lean",
    ) -> None:
        redact_solution_refs = effective_solution_placeholder_suppression(
            suppress_solution_placeholders=bool(
                self.suppress_solution_placeholders
            ),
            opaque_mode=bool(self.opaque_mode),
            allow_official_answer_visibility=bool(
                self.allow_official_answer_visibility
            ),
            official_answer_payload_present=(
                self.official_answer_payload_present
            ),
        )
        referenced_names: List[str] = []
        # Keep theorem-family choices without retaining rejected proof bodies
        # or local binder names. Qualified names are the useful, stable part of
        # a failed route (for example ``Fin.prod_univ_succ``).
        for match in re.finditer(
            r"(?<![\w'])((?:[A-Za-z_][A-Za-z0-9_']*\.)+"
            r"[A-Za-z_][A-Za-z0-9_']*)(?![\w'])",
            str(code or ""),
        ):
            name = str(match.group(1) or "").strip()
            safe_name = _prompt_safe_helper_name(
                name,
                redact_solution_refs=redact_solution_refs,
            )
            if (
                not name
                or safe_name != name
                or "_hidden_" in safe_name
                or name in referenced_names
            ):
                continue
            referenced_names.append(name)
            if len(referenced_names) >= 16:
                break
        self.scratch.append(
            ScratchRecord(
                turn_index=int(turn_index or 0),
                tool_call_index=int(tool_call_index or 0),
                ok=bool(ok),
                summary=" ".join(str(summary or "").split())[:500],
                code_hash=text_hash(code),
                normalized_code=(
                    normalize_scratch_code_for_registry(code) if ok else ""
                ),
                goal_hash=text_hash(
                    str(goal_statement or "").strip() or self.root_statement
                ),
                goal_key=canonical_dossier_statement_key(
                    str(goal_statement or "").strip() or self.root_statement
                ),
                referenced_names=referenced_names,
                source_label=str(source_label or "try_lean"),
            )
        )
        self.prune_scratch_records()
        if self.proof_graph is not None:
            self.proof_graph.record_scratch(
                turn_index=turn_index,
                tool_call_index=tool_call_index,
                ok=ok,
                summary=summary,
                code=code,
                label=source_label,
            )

    def prune_scratch_records(self) -> int:
        """Apply the aggregate scratch retention policy in memory."""

        retained = _bounded_scratch_records(self.scratch)
        removed = max(0, len(self.scratch) - len(retained))
        if removed:
            self.scratch = retained
            self.increment_tool_metric("mini_scratch_records_pruned", removed)
        return removed

    def record_accepted_proof_stub(
        self,
        *,
        turn_index: int,
        tool_call_index: int,
        goal_statement: str,
        preamble: str,
        context_lemmas: Iterable[str] = (),
        code: str,
    ) -> None:
        normalized = normalize_scratch_code_for_registry(code)
        if not normalized:
            return
        context_text = "\n".join(str(item or "") for item in list(context_lemmas or ()))
        record = AcceptedProofStub(
            turn_index=int(turn_index or 0),
            tool_call_index=int(tool_call_index or 0),
            goal_hash=text_hash(goal_statement),
            preamble_hash=text_hash(preamble),
            context_hash=text_hash(context_text),
            code_hash=text_hash(code),
            normalized_code=normalized,
        )
        key = (
            record.goal_hash,
            record.preamble_hash,
            record.context_hash,
            record.normalized_code,
        )
        for existing in self.accepted_proof_stubs:
            existing_key = (
                existing.goal_hash,
                existing.preamble_hash,
                existing.context_hash,
                existing.normalized_code,
            )
            if existing_key == key:
                return
        self.accepted_proof_stubs.append(record)
        del self.accepted_proof_stubs[:-16]

    def accepted_scratch_registry(self) -> List[Dict[str, Any]]:
        """Return durable accepted scratch checks, separated from failures."""

        return [asdict(item) for item in self.accepted_proof_stubs]

    def increment_tool_metric(self, key: str, amount: int = 1) -> None:
        name = str(key or "").strip()
        if not name:
            return
        increment = int(amount or 0)
        self.tool_metrics[name] = int(self.tool_metrics.get(name, 0) or 0) + increment
        sink = getattr(self, "_monotonic_tool_metric_sink", None)
        if callable(sink):
            try:
                sink(name, increment)
            except Exception:
                pass

    def record_parallel_sample_proof_state(
        self,
        record: Dict[str, Any],
        *,
        sample_index: int,
        role: str = "",
        selected: bool = False,
    ) -> None:
        """Preserve sibling sample frontier/scheduling state for later analysis."""

        if not isinstance(record, dict) or not record:
            return
        entry = dict(record)
        entry["sample_index"] = int(sample_index or 0)
        entry["sample_role"] = str(role or "")
        entry["selected_sample"] = bool(selected)
        self.parallel_sample_proof_states.append(entry)
        self.increment_tool_metric("mini_parallel_sample_proof_state_snapshots", 1)
        if isinstance(entry.get("graph_structural_summary"), dict):
            self.increment_tool_metric("mini_parallel_sample_structural_snapshots", 1)
        # Keep records bounded; each proof_state snapshot can be large.
        del self.parallel_sample_proof_states[:-8]

    def record_decl_application(
        self,
        *,
        turn_index: int,
        tool_call_index: int,
        statement: str,
        decl_name: str,
        applicable: bool,
        proof_stub: str = "",
        remaining_goals: Optional[Iterable[Any]] = None,
        error_kind: str = "",
        error_text: str = "",
        error_text_is_lean_diagnostic: Optional[bool] = None,
        decl_type: str = "",
    ) -> None:
        goals = [str(goal or "") for goal in (remaining_goals or [])]
        proof_stub_text = str(proof_stub or "").strip()
        answer_safety_kwargs = self._answer_safety_kwargs()
        lean_diagnostic_error = (
            _decl_application_error_is_lean_diagnostic(error_kind, error_text)
            if error_text_is_lean_diagnostic is None
            else bool(error_text_is_lean_diagnostic)
        )
        prompt_safe_proof_stub = (
            proof_stub_text
            if proof_stub_text
            and not is_answer_unsafe_statement_text(
                proof_stub_text,
                **answer_safety_kwargs,
            )
            else ""
        )
        closed = bool(applicable) and bool(prompt_safe_proof_stub) and not goals
        redact_solution_refs = bool(self.suppress_solution_placeholders)
        raw_decl_name = str(decl_name or "").strip()
        prompt_safe_decl_name = (
            _prompt_safe_helper_name(
                raw_decl_name,
                redact_solution_refs=redact_solution_refs,
            )
            if raw_decl_name
            else "<unknown>"
        )
        prompt_safe_statement_preview = _prompt_safe_lean_diagnostic_text(
            statement,
            limit=1000,
            redact_solution_refs=redact_solution_refs,
        )
        prompt_safe_goals = [
            _prompt_safe_lean_diagnostic_text(
                goal,
                limit=500,
                redact_solution_refs=redact_solution_refs,
            )
            for goal in goals[:5]
        ]
        prompt_safe_error_text = (
            _prompt_safe_lean_diagnostic_text(
                error_text,
                limit=500,
                redact_solution_refs=redact_solution_refs,
            )
            if lean_diagnostic_error
            else _prompt_safe_inline_text(
                error_text,
                limit=500,
                redact_solution_refs=redact_solution_refs,
            )
        )
        prompt_safe_decl_type = _prompt_safe_inline_text(
            decl_type,
            limit=500,
            redact_solution_refs=redact_solution_refs,
        )
        self.decl_applications.append(
            DeclApplicationRecord(
                turn_index=int(turn_index or 0),
                tool_call_index=int(tool_call_index or 0),
                decl_name=prompt_safe_decl_name,
                statement_hash=text_hash(statement),
                applicable=bool(applicable),
                closed=closed,
                remaining_goal_count=len(goals),
                proof_stub_hash=text_hash(proof_stub_text) if proof_stub_text else "",
                error_kind=str(error_kind or ""),
                statement_preview=prompt_safe_statement_preview,
                proof_stub=prompt_safe_proof_stub[:1000],
                remaining_goals_preview=prompt_safe_goals,
                error_text=prompt_safe_error_text,
                error_text_is_lean_diagnostic=lean_diagnostic_error,
                decl_type=prompt_safe_decl_type,
            )
        )
        if self.proof_graph is not None:
            self.proof_graph.record_decl_application(
                turn_index=turn_index,
                tool_call_index=tool_call_index,
                statement=prompt_safe_statement_preview,
                decl_name=prompt_safe_decl_name,
                applicable=applicable,
                proof_stub=prompt_safe_proof_stub,
                remaining_goals=prompt_safe_goals,
                error_kind=error_kind,
                error_text=prompt_safe_error_text,
                decl_type=prompt_safe_decl_type,
            )

    def _persist_solved_artifact(
        self,
        proof: str,
        *,
        replay_helpers: Optional[Iterable[str]] = None,
        support_helper_names: Optional[Iterable[str]] = None,
        root_certificate_metadata: Optional[Dict[str, Any]] = None,
        increment_certificate_metric: bool = True,
    ) -> None:
        raw_proof_text = str(proof or "")
        proof_text = sanitize_lean_artifact_text(raw_proof_text)
        raw_replay_helper_list = [
            str(block or "").strip()
            for block in list(replay_helpers or ())
            if str(block or "").strip()
        ]
        replay_helper_list = list(sanitize_lean_artifact_texts(raw_replay_helper_list))
        if support_helper_names is None:
            support_names = self._canonical_support_names(
                self._referenced_verified_helper_names(proof_text)
            )
        else:
            support_names = [
                str(name or "").strip()
                for name in list(support_helper_names or ())
                if str(name or "").strip()
            ]
        raw_replay_closure = self.root_replay_helper_closure(
            replay_helpers=replay_helper_list,
            support_helper_names=support_names,
        )
        replay_closure = list(sanitize_lean_artifact_texts(raw_replay_closure))
        certificate_metadata = dict(root_certificate_metadata or {})
        certificate_metadata.setdefault(
            "artifact_proof_sanitized",
            raw_proof_text != proof_text,
        )
        certificate_metadata.setdefault("artifact_proof_hash", text_hash(proof_text))
        if raw_proof_text and raw_proof_text != proof_text:
            certificate_metadata.setdefault("source_proof_hash", text_hash(raw_proof_text))
        certificate_metadata.setdefault(
            "artifact_replay_helpers_sanitized",
            tuple(raw_replay_helper_list) != tuple(replay_helper_list)
            or tuple(raw_replay_closure) != tuple(replay_closure),
        )
        self._root_proof_finalization_receipts.clear()
        self.final_proof = proof_text
        self.final_proof_hash = text_hash(proof_text)
        self.final_replay_helpers = replay_closure
        self.root_proof_certificate = self._root_proof_certificate(
            proof=proof_text,
            replay_helpers=self.final_replay_helpers,
            support_helper_names=support_names,
            metadata=certificate_metadata,
        )
        if increment_certificate_metric:
            self.increment_tool_metric("mini_root_certificate_created", 1)
        if self.proof_graph is not None:
            replay_helper_names = [
                name
                for block in self.final_replay_helpers
                for name in [helper_decl_name(block)]
                if name
            ]
            self.proof_graph.mark_root_solved(
                proof=proof_text,
                replay_helper_names=replay_helper_names,
                support_helper_names=support_names,
            )

    def mark_solved(
        self,
        proof: str,
        *,
        replay_helpers: Optional[Iterable[str]] = None,
        support_helper_names: Optional[Iterable[str]] = None,
        root_certificate_metadata: Optional[Dict[str, Any]] = None,
    ) -> None:
        self._persist_solved_artifact(
            proof,
            replay_helpers=replay_helpers,
            support_helper_names=support_helper_names,
            root_certificate_metadata=root_certificate_metadata,
            increment_certificate_metric=True,
        )

    def rewrite_solved_artifact(
        self,
        proof: str,
        *,
        replay_helpers: Optional[Iterable[str]] = None,
        support_helper_names: Optional[Iterable[str]] = None,
        root_certificate_metadata: Optional[Dict[str, Any]] = None,
    ) -> None:
        """Refresh durable root artifacts without recording a new solve metric."""

        self._persist_solved_artifact(
            proof,
            replay_helpers=replay_helpers,
            support_helper_names=support_helper_names,
            root_certificate_metadata=root_certificate_metadata,
            increment_certificate_metric=False,
        )

    def clear_solved(self) -> None:
        self._root_proof_finalization_receipts.clear()
        self.final_proof = None
        self.final_proof_hash = None
        self.final_replay_helpers = []
        self.root_proof_certificate = None
        if self.proof_graph is not None:
            self.proof_graph.clear_root_solved()

    def record_graph_event(self, record: Dict[str, Any]) -> Optional[Dict[str, Any]]:
        """Fold structured recorder events into the proof graph.

        This keeps graph state near the dossier API.  The mini recursive
        controller can continue emitting auditable records while the dossier
        turns those records into nodes, attempts, and edges.
        """
        if self.proof_graph is None:
            return
        phase = str(record.get("phase", "") or "")
        verdict = str(record.get("verdict", "") or "")
        ready_route_ids_before_projection = self._ready_route_ids()
        target_statuses_before_projection = {
            node.node_id: node.status
            for node in self.proof_graph.nodes.values()
            if node.kind
            in {
                "proposed_claim",
                "formal_variant",
                "missing_obligation",
            }
        }

        def projected_target_node_ids() -> List[str]:
            return [
                node.node_id
                for node in self.proof_graph.nodes.values()
                if node.kind
                in {
                    "proposed_claim",
                    "formal_variant",
                    "missing_obligation",
                }
                and (
                    node.node_id not in target_statuses_before_projection
                    or (
                        node.status == "proved"
                        and target_statuses_before_projection.get(node.node_id)
                        != "proved"
                    )
                )
            ]

        if (
            phase == "mini_recursive_route_contract"
            and verdict == "root_route_contract_declared"
        ):
            projection = self._record_mini_recursive_route_contract_event(record)
            self.reconcile_verified_facts(
                trigger="route_contract_projection",
                ready_before=ready_route_ids_before_projection,
                projected_node_ids=projected_target_node_ids(),
            )
            self.reconcile_invalidated_graph_targets()
            self.reconcile_proof_idea_graph_statuses()
            return projection
        if (
            phase == "mini_recursive_claim_invalidated"
            and verdict == "claim_invalidated_by_child"
        ):
            invalidated_statement = str(record.get("statement", "") or "").strip()
            # The certificate boundary must have populated the tombstone
            # before this graph-observability event arrives. Never recreate
            # authority from a recorder verdict alone (including replayed
            # legacy events).
            if invalidated_statement and not self.invalidated_statement_reason(
                invalidated_statement
            ):
                return
        if verdict == "variant_falsified_by_sample":
            # Legacy event retained for trace readability only. Concrete
            # samples predating the certificate ledger are not durable proof.
            return
        graph_native = self._record_mini_recursive_graph_native_event(record)
        self.reconcile_verified_facts(
            trigger="graph_event_projection",
            ready_before=ready_route_ids_before_projection,
            projected_node_ids=projected_target_node_ids(),
        )
        self.reconcile_invalidated_graph_targets()
        self.reconcile_proof_idea_graph_statuses()
        if str(graph_native.get("skip_helper_attempt") or "").strip():
            return
        if phase == "mini_recursive_claim" or (
            phase == "mini_recursive_claim_variant"
            and not str(record.get("helper_name", "") or "").strip()
        ):
            claim_id = str(graph_native.get("claim_id") or "").strip()
            target_id = str(
                graph_native.get("variant_id")
                or claim_id
                or graph_native.get("route_id")
                or ""
            ).strip()
            error_type = self._mini_recursive_failure_error_type(record)
            attempt_metadata = {
                "pass_index": record.get("pass_index"),
                "claim_index": record.get("claim_index"),
                "variant_index": record.get("variant_index"),
                "claim_name": record.get("claim_name"),
            }
            if target_id and target_id in self.proof_graph.nodes:
                self.proof_graph.record_attempt(
                    target_id,
                    phase=phase,
                    turn_index=int(record.get("turn_in_phase", 0) or 0),
                    proof="",
                    verdict=verdict,
                    error_type=error_type,
                    metadata=attempt_metadata,
                )
            if (
                phase == "mini_recursive_claim"
                and claim_id
                and claim_id != target_id
                and claim_id in self.proof_graph.nodes
            ):
                self.proof_graph.record_attempt(
                    claim_id,
                    phase=phase,
                    turn_index=int(record.get("turn_in_phase", 0) or 0),
                    proof="",
                    verdict=verdict,
                    error_type=error_type,
                    metadata=attempt_metadata,
                )
            return
        if (
            phase == "mini_recursive_claim_invalidated"
            and verdict
            in {
                "claim_skipped_previous_child_invalidation",
                "claim_skipped_repaired_previous_child_invalidation",
            }
        ) or (
            phase == "mini_recursive_proposed_helper"
            and verdict == "proposed_helper_skipped_child_invalidated"
        ):
            statement = str(record.get("statement", "") or "").strip()
            key = canonical_dossier_statement_key(statement)
            target = None
            if key:
                for node in self.proof_graph.nodes.values():
                    if node.kind != "helper":
                        continue
                    if canonical_dossier_statement_key(node.statement) == key:
                        target = node
                        break
            if target is None:
                helper_name = (
                    str(record.get("helper_name", "") or "").strip()
                    or str(record.get("proposed_helper", "") or "").strip()
                    or f"invalidated_{text_hash(key)}"
                )
                target = self.proof_graph.ensure_helper(
                    helper_name,
                    statement=statement,
                    phase=phase,
                    turn_index=int(record.get("turn_in_phase", 0) or 0),
                    metadata={
                        "invalid_reason": record.get("invalid_reason"),
                        "proposed_helper": record.get("proposed_helper"),
                        "claim_name": record.get("claim_name"),
                    },
                )
            self.proof_graph.record_attempt(
                target.node_id,
                phase=phase,
                turn_index=int(record.get("turn_in_phase", 0) or 0),
                proof="",
                verdict=verdict,
                error_type=(
                    "previous_child_invalidation"
                    if phase == "mini_recursive_claim_invalidated"
                    else "invalidated_proposed_helper_suppressed"
                ),
                metadata={
                    "pass_index": record.get("pass_index"),
                    "claim_index": record.get("claim_index"),
                    "variant_index": record.get("variant_index"),
                    "claim_name": record.get("claim_name"),
                    "proposed_helper": record.get("proposed_helper"),
                    "invalid_reason": record.get("invalid_reason"),
                },
            )
            variant_node_id = str(graph_native.get("variant_id") or "").strip()
            if variant_node_id and variant_node_id in self.proof_graph.nodes:
                self.proof_graph.record_attempt(
                    variant_node_id,
                    phase=phase,
                    turn_index=int(record.get("turn_in_phase", 0) or 0),
                    proof="",
                    verdict=verdict,
                    error_type=(
                        "previous_child_invalidation"
                        if phase == "mini_recursive_claim_invalidated"
                        else "invalidated_proposed_helper_suppressed"
                    ),
                    metadata={
                        "pass_index": record.get("pass_index"),
                        "claim_index": record.get("claim_index"),
                        "variant_index": record.get("variant_index"),
                        "claim_name": record.get("claim_name"),
                        "proposed_helper": record.get("proposed_helper"),
                        "invalid_reason": record.get("invalid_reason"),
                    },
                )
            return
        if phase in {
            "mini_recursive_claim_variant",
            "mini_recursive_claim_dependency",
            "mini_recursive_claim_typecheck",
            "mini_recursive_claim_sample",
            "mini_recursive_claim_tactic",
            "mini_recursive_claim_llm",
            "mini_recursive_claim_invalidated",
            "mini_recursive_claim_reuse",
        }:
            helper_name = str(record.get("helper_name", "") or "").strip()
            statement = str(record.get("statement", "") or "").strip()
            if not helper_name:
                return
            node = self.proof_graph.ensure_helper(
                helper_name,
                statement=statement,
                phase=phase,
                turn_index=int(record.get("turn_in_phase", 0) or 0),
                metadata={
                    "pass_index": record.get("pass_index"),
                    "claim_index": record.get("claim_index"),
                    "variant_index": record.get("variant_index"),
                    "variant_mode": record.get("mode")
                    or record.get("variant_mode"),
                    "claim_name": record.get("claim_name"),
                    "dependencies": list(record.get("dependencies", []) or []),
                    "missing_dependencies": list(
                        record.get("missing_dependencies", []) or []
                    ),
                    "sample_reason": record.get("reason"),
                    "sample_falsified": record.get("falsified"),
                    "invalid_reason": record.get("invalid_reason"),
                },
            )
            success = record.get("tactic_success_attempt") or {}
            proof = str(success.get("proof", "") or "")
            error_type = ""
            attempts = list(record.get("tactic_attempts", []) or [])
            if attempts and isinstance(attempts[0], dict):
                error_type = str(attempts[0].get("error_type", "") or "")
            if phase == "mini_recursive_claim_typecheck":
                error_type = "type_rejected" if verdict == "variant_type_rejected" else ""
            elif phase == "mini_recursive_claim_sample":
                error_type = (
                    "sample_falsified"
                    if verdict == "variant_falsified_by_sample"
                    else ""
                )
            elif phase == "mini_recursive_claim_dependency":
                error_type = "unproved_dependency"
            elif phase == "mini_recursive_claim_invalidated":
                error_type = (
                    "child_invalidated_claim"
                    if verdict == "claim_invalidated_by_child"
                    else "previous_child_invalidation"
                )
            self.proof_graph.record_attempt(
                node.node_id,
                phase=phase,
                turn_index=int(record.get("turn_in_phase", 0) or 0),
                proof=proof,
                verdict=verdict,
                error_type=error_type,
                metadata={
                    "pass_index": record.get("pass_index"),
                    "claim_index": record.get("claim_index"),
                    "variant_index": record.get("variant_index"),
                    "tactic_candidate_count": record.get("tactic_candidate_count"),
                    "tactic_exit_reason": record.get("tactic_exit_reason"),
                    "invalid_reason": record.get("invalid_reason"),
                },
            )
            variant_node_id = str(graph_native.get("variant_id") or "").strip()
            if variant_node_id and variant_node_id in self.proof_graph.nodes:
                self.proof_graph.record_attempt(
                    variant_node_id,
                    phase=phase,
                    turn_index=int(record.get("turn_in_phase", 0) or 0),
                    proof=proof,
                    verdict=verdict,
                    error_type=error_type,
                    metadata={
                        "pass_index": record.get("pass_index"),
                        "claim_index": record.get("claim_index"),
                        "variant_index": record.get("variant_index"),
                        "helper_name": helper_name,
                        "claim_name": record.get("claim_name"),
                        "tactic_candidate_count": record.get("tactic_candidate_count"),
                        "tactic_exit_reason": record.get("tactic_exit_reason"),
                        "invalid_reason": record.get("invalid_reason"),
                    },
                )
            return

        if phase == "mini_recursive_root_tactic":
            success = record.get("tactic_success_attempt") or {}
            proof = str(success.get("proof", "") or "")
            effective_verdict = verdict
            if verdict == "tactic_solved" and not proof:
                effective_verdict = "tactic_rejected"
            error_type = ""
            attempts = list(record.get("tactic_attempts", []) or [])
            if attempts and isinstance(attempts[0], dict):
                error_type = str(attempts[0].get("error_type", "") or "")
            after_helper = str(record.get("after_helper", "") or "")
            helper_names = [after_helper] if after_helper and after_helper != "pre_plan" else []
            self.proof_graph.record_attempt(
                self.proof_graph.root_node_id,
                phase=phase,
                turn_index=int(record.get("turn_in_phase", 0) or 0),
                proof=proof,
                helper_names=helper_names,
                verdict=effective_verdict,
                error_type=error_type,
                metadata={
                    "pass_index": record.get("pass_index"),
                    "after_helper": after_helper,
                    "tactic_candidate_count": record.get("tactic_candidate_count"),
                    "tactic_exit_reason": record.get("tactic_exit_reason"),
                    "active_root_target_statement": record.get(
                        "active_root_target_statement"
                    ),
                    "active_root_lift_attempted": record.get(
                        "active_root_lift_attempted"
                    ),
                    "active_root_lift_succeeded": record.get(
                        "active_root_lift_succeeded"
                    ),
                    "active_root_fallback_attempted": record.get(
                        "active_root_fallback_attempted"
                    ),
                    "active_root_fallback_succeeded": record.get(
                        "active_root_fallback_succeeded"
                    ),
                },
            )

    def _record_mini_recursive_route_contract_event(
        self,
        record: Dict[str, Any],
    ) -> Dict[str, str]:
        """Project a mini-recursive pass into an explicit root route contract."""

        if self.proof_graph is None:
            return {}
        claims: List[Dict[str, Any]] = [
            dict(item)
            for item in list(record.get("accepted_claims") or [])
            if isinstance(item, dict)
        ]
        root_assembly_claim_names = {
            str(name or "").strip()
            for name in list(record.get("root_assembly_claim_names") or [])
            if str(name or "").strip()
        }
        root_contract_statement = str(
            record.get("root_contract_statement") or ""
        ).strip()
        root_contract_identity = _bound_mini_recursive_event_contract_identity(
            record,
            prefix="root_",
            statement=root_contract_statement,
        )
        parsed_root_contract_identity = parse_lean_contract_identity(
            root_contract_identity
        )
        root_contract_environment_hash = str(
            record.get("root_contract_identity_environment_hash") or ""
        ).strip()
        if (
            _mini_recursive_event_contract_evidence_present(record, prefix="root_")
            and not root_contract_identity
        ):
            self.increment_tool_metric(
                "mini_recursive_route_contracts_invalid_root_identity_rejected",
                1,
            )
            return {}
        if root_contract_identity and str(
            record.get("root_contract_identity_statement_key") or ""
        ).strip() != graph_statement_key(self.root_statement):
            self.increment_tool_metric(
                "mini_recursive_route_contracts_invalid_root_identity_rejected",
                1,
            )
            return {}
        route_anchor_identities = set()
        validated_route_anchor_contracts: List[Dict[str, str]] = []
        route_anchors_present = "route_anchor_contracts" in record
        raw_route_anchors = record.get("route_anchor_contracts")
        if not route_anchors_present:
            raw_route_anchors = ()
        if not isinstance(raw_route_anchors, Sequence) or isinstance(
            raw_route_anchors,
            (str, bytes),
        ):
            self.increment_tool_metric(
                "mini_recursive_route_contracts_invalid_anchor_universe_rejected",
                1,
            )
            return {}
        advertised_route_anchors = list(raw_route_anchors)
        invalid_route_anchor = False
        for anchor in advertised_route_anchors:
            if not isinstance(anchor, Mapping):
                invalid_route_anchor = True
                continue
            anchor_statement = str(anchor.get("statement") or "").strip()
            anchor_identity = _bound_mini_recursive_event_contract_identity(
                anchor,
                statement=anchor_statement,
            )
            if (
                anchor_identity
                and str(anchor.get("contract_identity_environment_hash") or "").strip()
                == root_contract_environment_hash
            ):
                route_anchor_identities.add(anchor_identity)
                validated_route_anchor_contracts.append({
                    "statement": anchor_statement,
                    "contract_identity": anchor_identity,
                    "contract_identity_statement_key": str(
                        anchor.get("contract_identity_statement_key") or ""
                    ).strip(),
                    "contract_identity_environment_hash": str(
                        anchor.get("contract_identity_environment_hash") or ""
                    ).strip(),
                    "contract_identity_evidence_receipt": str(
                        anchor.get("contract_identity_evidence_receipt") or ""
                    ).strip(),
                })
            else:
                invalid_route_anchor = True
        current_anchor_identities = set()
        current_active_targets = self.active_root_targets_for_current_frame()
        current_targets_use_contract_evidence = any(
            _mini_recursive_event_contract_evidence_present(active_target)
            for active_target in current_active_targets
        )
        invalid_current_anchor = False
        for active_target in current_active_targets:
            closed_target_statements = active_root_equivalence_statements(
                [active_target]
            )
            target_statement = (
                closed_target_statements[0]
                if len(closed_target_statements) == 1
                else ""
            )
            target_identity = _bound_mini_recursive_event_contract_identity(
                active_target,
                statement=target_statement,
            )
            if (
                target_identity
                and str(
                    active_target.get("contract_identity_environment_hash") or ""
                ).strip()
                == root_contract_environment_hash
            ):
                current_anchor_identities.add(target_identity)
            elif current_targets_use_contract_evidence:
                invalid_current_anchor = True
        if (
            invalid_route_anchor
            or invalid_current_anchor
            or (
                current_anchor_identities
                and route_anchor_identities != current_anchor_identities
            )
        ):
            self.increment_tool_metric(
                "mini_recursive_route_contracts_invalid_anchor_universe_rejected",
                1,
            )
            return {}

        def is_root_terminal_claim(item: Mapping[str, Any]) -> bool:
            name = str(item.get("name") or item.get("claim_name") or "").strip()
            statement = str(item.get("statement") or "").strip()
            if not name or not statement:
                return False
            claim_contract_identity = (
                _bound_mini_recursive_event_contract_identity(
                    item,
                    statement=statement,
                )
            )
            if (
                _mini_recursive_event_contract_evidence_present(item)
                and not claim_contract_identity
            ):
                return False
            parsed_claim_contract_identity = parse_lean_contract_identity(
                claim_contract_identity
            )
            relation_match = _mini_recursive_event_route_relation_is_valid(
                item,
                root_contract_identity=root_contract_identity,
                root_environment_hash=root_contract_environment_hash,
                statement=statement,
                allowed_anchor_identities=tuple(route_anchor_identities),
            )
            if relation_match:
                return True
            relation_evidence_present = any(
                str(item.get(field) or "").strip()
                for field in (
                    "contract_route_relation_kind",
                    "contract_route_relation_anchor_identity",
                    "contract_route_relation_evidence_receipt",
                )
            )
            if relation_evidence_present:
                # A partial, stale, or forged relation is not a legacy event.
                # It must fail closed instead of falling through to a weaker
                # surface recognizer that ignores the broken certificate.
                return False
            claim_environment_hash = str(
                item.get("contract_identity_environment_hash") or ""
            ).strip()
            # Receipt-bound contradictions are authoritative. Do not let a
            # looser surface comparison erase a different Expr identity or
            # cross an environment boundary merely because printers happen
            # to emit the same text.
            if parsed_root_contract_identity and parsed_claim_contract_identity:
                if (
                    root_contract_identity != claim_contract_identity
                    or root_contract_environment_hash
                    != claim_environment_hash
                ):
                    return False
                root_surface_key = _mini_recursive_contract_statement_key(
                    root_contract_statement or self.root_statement
                )
                claim_surface_key = _mini_recursive_contract_statement_key(
                    statement
                )
                if root_surface_key != claim_surface_key:
                    # Equal identities attached to printer-divergent source
                    # are not self-authenticating. Only the Lean-produced
                    # relation receipt may connect those two event surfaces.
                    return False
            return bool(
                graph_statement_root_equivalent(
                    statement,
                    self.root_statement,
                    active_target_statements=(self.root_statement,),
                )
                or graph_statement_is_root_bridge(statement, self.root_statement)
            )

        if not root_assembly_claim_names:
            # Legacy events did not name their terminal explicitly. Preserve
            # only contracts whose accepted claims contain an exact/root-
            # equivalent terminal; helper-only historical events must not be
            # replayed into executable routes merely because their verdict was
            # incorrectly labelled as a declaration.
            root_assembly_claim_names = {
                str(item.get("name") or item.get("claim_name") or "").strip()
                for item in claims
                if is_root_terminal_claim(item)
            }
        def claim_order(position: int) -> int:
            raw = claims[position].get("selected_index", position + 1)
            try:
                return int(raw)
            except (TypeError, ValueError):
                return position + 1

        def source_order(position: int) -> int:
            raw = claims[position].get("source_index", position + 1)
            try:
                return int(raw)
            except (TypeError, ValueError):
                return position + 1

        terminal_positions = [
            position
            for position, item in enumerate(claims)
            if str(item.get("name") or item.get("claim_name") or "").strip()
            in root_assembly_claim_names
            and is_root_terminal_claim(item)
        ]
        selected_terminal_index = record.get(
            "_root_assembly_claim_selected_index"
        )
        if selected_terminal_index is not None:
            try:
                selected_terminal_index = int(selected_terminal_index)
            except (TypeError, ValueError):
                return {}
            terminal_positions = [
                position
                for position in terminal_positions
                if claim_order(position) == selected_terminal_index
            ]
        if not root_assembly_claim_names or not terminal_positions:
            self.increment_tool_metric(
                "mini_recursive_route_contracts_missing_root_terminal_rejected",
                1,
            )
            return {}
        claim_positions_by_name: Dict[str, List[int]] = {}
        for position, item in enumerate(claims):
            claim_name = str(
                item.get("name") or item.get("claim_name") or ""
            ).strip()
            if claim_name:
                claim_positions_by_name.setdefault(claim_name, []).append(position)
        satisfied_dependency_records = [
            dict(item)
            for item in list(record.get("satisfied_dependency_helpers") or [])
            if isinstance(item, dict)
        ]
        verified_satisfied_dependency_names: Set[str] = set()
        for item in satisfied_dependency_records:
            claim_name = str(
                item.get("claim_name") or item.get("helper_name") or ""
            ).strip()
            helper_name = str(
                item.get("helper_name") or item.get("claim_name") or ""
            ).strip()
            source_hash = str(item.get("source_hash") or "").strip()
            helper = self.verified_helpers.get(helper_name)
            if helper is not None and not source_hash:
                source_hash = str(
                    getattr(helper, "source_hash", "") or ""
                ).strip()
            if (
                claim_name
                and helper is not None
                and source_hash
                and source_hash
                == str(getattr(helper, "source_hash", "") or "").strip()
            ):
                verified_satisfied_dependency_names.add(claim_name)

        def dependency_closure_variants(
            position: int,
            visiting: frozenset[int] = frozenset(),
        ) -> List[frozenset[int]]:
            if position in visiting:
                return []
            variants = [frozenset({position})]
            next_visiting = visiting | {position}
            for dependency in list(claims[position].get("dependencies") or []):
                dependency_name = str(dependency or "").strip()
                candidates = claim_positions_by_name.get(dependency_name, [])
                preceding = [
                    candidate
                    for candidate in candidates
                    if claim_order(candidate) < claim_order(position)
                ]
                candidate_positions = preceding or (
                    candidates if len(candidates) == 1 else []
                )
                if not candidate_positions:
                    # A dependency may be satisfied by a verified helper from a
                    # prior pass rather than another claim in this event.
                    if dependency_name in verified_satisfied_dependency_names:
                        continue
                    return []
                dependency_variants: List[frozenset[int]] = []
                for candidate in candidate_positions:
                    dependency_variants.extend(
                        dependency_closure_variants(candidate, next_visiting)
                    )
                if not dependency_variants:
                    return []
                combined = {
                    current | dependency_variant
                    for current in variants
                    for dependency_variant in dependency_variants
                }
                if len(combined) > 128:
                    return []
                variants = sorted(
                    combined,
                    key=lambda positions: tuple(
                        sorted(
                            (
                                claim_order(item),
                                source_order(item),
                                item,
                            )
                            for item in positions
                        )
                    ),
                )
            return variants

        route_variants: List[Tuple[int, frozenset[int]]] = []
        for terminal_position in sorted(
            terminal_positions,
            key=lambda position: (
                claim_order(position),
                source_order(position),
                position,
            ),
        ):
            for closure in dependency_closure_variants(terminal_position):
                variant = (terminal_position, closure)
                if variant not in route_variants:
                    route_variants.append(variant)
                if len(route_variants) > 128:
                    self.increment_tool_metric(
                        "mini_recursive_route_contracts_alternative_cap_rejected",
                        1,
                    )
                    return {}
        if not route_variants:
            return {}
        if len(route_variants) > 1:
            projected_route_ids: List[str] = []
            for terminal_position, closure in route_variants:
                branch_record = copy.deepcopy(record)
                branch_record["accepted_claims"] = [
                    copy.deepcopy(item)
                    for position, item in enumerate(claims)
                    if position in closure
                ]
                branch_record["root_assembly_claim_names"] = [
                    str(
                        claims[terminal_position].get("name")
                        or claims[terminal_position].get("claim_name")
                        or ""
                    ).strip()
                ]
                branch_record["_root_assembly_claim_selected_index"] = (
                    claim_order(terminal_position)
                )
                projection = self._record_mini_recursive_route_contract_event(
                    branch_record
                )
                route_id = str(projection.get("route_id") or "").strip()
                if route_id and route_id not in projected_route_ids:
                    projected_route_ids.append(route_id)
            return (
                {"route_id": projected_route_ids[0]}
                if projected_route_ids
                else {}
            )
        terminal_position, required_claim_positions = route_variants[0]
        terminal_positions = [terminal_position]
        terminal_claims = [claims[terminal_position]]
        root_assembly_claim_names = {
            str(
                terminal_claims[0].get("name")
                or terminal_claims[0].get("claim_name")
                or ""
            ).strip()
        }
        claims = [
            item
            for position, item in enumerate(claims)
            if position in required_claim_positions
        ]
        required_dependency_names = {
            str(dependency or "").strip()
            for item in claims
            for dependency in list(item.get("dependencies") or [])
            if str(dependency or "").strip()
        }
        validated_relation_anchors = {
            str(item.get("contract_route_relation_anchor_identity") or "").strip()
            for item in terminal_claims
            if _mini_recursive_event_route_relation_is_valid(
                item,
                root_contract_identity=root_contract_identity,
                root_environment_hash=root_contract_environment_hash,
                statement=str(item.get("statement") or "").strip(),
                allowed_anchor_identities=tuple(route_anchor_identities),
            )
        }
        if (
            route_anchor_identities
            and root_contract_identity not in validated_relation_anchors
            and not route_anchor_identities.issubset(validated_relation_anchors)
        ):
            self.increment_tool_metric(
                "mini_recursive_route_contracts_missing_root_terminal_rejected",
                1,
            )
            return {}
        pass_index = record.get("pass_index")
        root_statement_identity = structural_statement_identity(
            self.root_statement,
            contract_identity=root_contract_identity,
            statement_key=canonical_dossier_statement_key(self.root_statement),
        )
        strategy_text = str(record.get("strategy") or "").strip()
        claim_statement_identities: Dict[str, str] = {}
        route_shape_claims: List[Dict[str, Any]] = []
        for item in claims:
            claim_name = str(
                item.get("name") or item.get("claim_name") or ""
            ).strip()
            statement = str(item.get("statement") or "").strip()
            statement_identity = structural_statement_identity(
                statement,
                contract_identity=_bound_mini_recursive_event_contract_identity(
                    item,
                    statement=statement,
                ),
                statement_key=canonical_dossier_statement_key(statement),
            )
            if claim_name and statement_identity:
                claim_statement_identities[claim_name] = statement_identity
            route_shape_claims.append(
                {
                    "statement_identity": statement_identity,
                    "role": str(item.get("role") or "").strip(),
                    "dependency_labels": [
                        str(value or "").strip()
                        for value in list(item.get("dependencies") or [])
                        if str(value or "").strip()
                    ],
                }
            )
        for item in route_shape_claims:
            item["dependency_statement_identities"] = sorted(
                claim_statement_identities.get(label, f"unresolved:{label}")
                for label in item.pop("dependency_labels")
            )
        route_shape_claims.sort(
            key=lambda item: (
                str(item.get("statement_identity") or ""),
                str(item.get("role") or ""),
                tuple(item.get("dependency_statement_identities") or ()),
            )
        )
        route_shape_identity = stable_identity(
            "mini-recursive-route-shape",
            root_statement_identity,
            json.dumps(
                route_shape_claims,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=True,
            ),
        )
        idea_strategy = strategy_text or "mini_recursive_plan"
        strategy_lineage_id = strategy_lineage_identity(
            theorem_name=self.theorem_name,
            root_statement_identity=root_statement_identity,
            strategy=idea_strategy,
            pass_index=pass_index,
        )
        proof_idea_id = proof_idea_identity(
            theorem_name=self.theorem_name,
            root_statement_identity=root_statement_identity,
            strategy=idea_strategy,
            route_shape_identity=route_shape_identity,
        )
        raw_deliberation = record.get("planner_deliberation")
        deliberation: Dict[str, Any] = {}
        if isinstance(raw_deliberation, Mapping):
            for field_name in (
                "routes",
                "bottlenecks",
                "candidate_lemmas",
                "falsification_targets",
            ):
                raw_values = raw_deliberation.get(field_name)
                if isinstance(raw_values, Sequence) and not isinstance(
                    raw_values,
                    (str, bytes),
                ):
                    values = [
                        str(value or "").strip()
                        for value in raw_values
                        if str(value or "").strip()
                    ]
                    if values:
                        deliberation[field_name] = values
            deliberation_note = str(raw_deliberation.get("notes") or "").strip()
            if deliberation_note:
                deliberation["notes"] = deliberation_note
            for field_name in ("trigger", "model_id", "assistant_content"):
                value = str(raw_deliberation.get(field_name) or "").strip()
                if value:
                    deliberation[field_name] = value
            for field_name in (
                "pass_index",
                "helpers_seen",
                "reasoning_tokens",
            ):
                raw_value = raw_deliberation.get(field_name)
                if (
                    isinstance(raw_value, int)
                    and not isinstance(raw_value, bool)
                    and raw_value >= 0
                ):
                    deliberation[field_name] = raw_value
        satisfied_dependency_helpers = [
            dict(item)
            for item in list(record.get("satisfied_dependency_helpers") or [])
            if isinstance(item, dict)
            and str(
                item.get("claim_name") or item.get("helper_name") or ""
            ).strip()
            in required_dependency_names
        ]
        required_helper_names = sorted(
            {
                str(
                    item.get("helper_name") or item.get("claim_name") or ""
                ).strip()
                for item in satisfied_dependency_helpers
                if str(
                    item.get("helper_name") or item.get("claim_name") or ""
                ).strip()
            }
        )
        required_helper_source_hashes: Dict[str, str] = {}
        for item in satisfied_dependency_helpers:
            helper_name = str(
                item.get("helper_name") or item.get("claim_name") or ""
            ).strip()
            source_hash = str(item.get("source_hash") or "").strip()
            if helper_name and not source_hash:
                helper = self.verified_helpers.get(helper_name)
                source_hash = str(
                    getattr(helper, "source_hash", "") or ""
                ).strip()
            if helper_name and source_hash:
                required_helper_source_hashes[helper_name] = source_hash
        required_node_ids: List[str] = []
        contract_claims: List[Dict[str, Any]] = []
        for index, item in enumerate(claims, start=1):
            name = str(item.get("name") or item.get("claim_name") or "").strip()
            statement = str(item.get("statement") or "").strip()
            selected_index = item.get("selected_index", index)
            source_index = item.get("source_index", selected_index)
            claim_key = _mini_recursive_claim_obligation_key(
                pass_index=pass_index,
                selected_index=selected_index,
                name=name,
                statement=statement,
            )
            if not claim_key:
                continue
            node_id = self.proof_graph.claim_node_id(claim_key)
            statement_key = _mini_recursive_contract_statement_key(statement)
            if node_id not in required_node_ids:
                required_node_ids.append(node_id)
            dependencies = sorted(
                {
                    str(dep or "").strip()
                    for dep in list(item.get("dependencies") or [])
                    if str(dep or "").strip()
                }
            )
            contract_claims.append(
                {
                    "name": name,
                    "statement": statement,
                    "role": str(item.get("role") or "").strip(),
                    "rationale": str(item.get("rationale") or "").strip(),
                    "invariant_refs": [
                        str(value or "").strip()
                        for value in list(item.get("invariant_refs") or [])
                        if str(value or "").strip()
                    ],
                    "sanity_check": str(
                        item.get("sanity_check") or ""
                    ).strip(),
                    "counting_classification": str(
                        item.get("counting_classification") or ""
                    ).strip(),
                    "variants": [
                        copy.deepcopy(value)
                        for value in list(item.get("variants") or [])
                        if isinstance(value, dict)
                        and str(value.get("statement") or "").strip()
                    ],
                    "obligation_id": str(
                        item.get("obligation_id") or ""
                    ).strip(),
                    "origin_plan_fingerprint": str(
                        item.get("origin_plan_fingerprint") or ""
                    ).strip(),
                    "dependency_semantic_identities": [
                        copy.deepcopy(value)
                        for value in list(
                            item.get("dependency_semantic_identities") or []
                        )
                        if isinstance(value, (list, tuple))
                        and len(value) == 2
                    ],
                    "statement_key": statement_key,
                    "contract_identity": str(
                        item.get("contract_identity") or ""
                    ).strip(),
                    "contract_identity_statement_key": str(
                        item.get("contract_identity_statement_key") or ""
                    ).strip(),
                    "contract_identity_environment_hash": str(
                        item.get("contract_identity_environment_hash") or ""
                    ).strip(),
                    "contract_identity_evidence_receipt": str(
                        item.get("contract_identity_evidence_receipt") or ""
                    ).strip(),
                    "contract_route_relation_kind": str(
                        item.get("contract_route_relation_kind") or ""
                    ).strip(),
                    "contract_route_relation_anchor_identity": str(
                        item.get("contract_route_relation_anchor_identity") or ""
                    ).strip(),
                    "contract_route_relation_evidence_receipt": str(
                        item.get("contract_route_relation_evidence_receipt") or ""
                    ).strip(),
                    "contract_display_statement": str(
                        item.get("contract_display_statement") or ""
                    ).strip(),
                    "contract_binder_sorts": [
                        str(value or "")
                        for value in list(
                            item.get("contract_binder_sorts") or []
                        )
                        if str(value or "").strip()
                    ],
                    "contract_proof_binder_types": [
                        str(value or "")
                        for value in list(
                            item.get("contract_proof_binder_types") or []
                        )
                        if str(value or "").strip()
                    ],
                    "claim_key": claim_key,
                    "claim_node_id": node_id,
                    "strategy_lineage_id": strategy_lineage_id,
                    "statement_identity": structural_statement_identity(
                        statement,
                        contract_identity=str(
                            item.get("contract_identity") or ""
                        ),
                        statement_key=statement_key,
                    ),
                    "dependencies": dependencies,
                    "source_index": source_index,
                    "selected_index": selected_index,
                }
            )
        if not required_node_ids:
            return {}
        turn_index = int(record.get("turn_in_phase", record.get("turn_index", 0)) or 0)
        contract_instance_key = _mini_recursive_route_contract_identity(
            pass_index=pass_index,
            contract_claims=contract_claims,
        )
        branch_id = str(record.get("branch_id") or "").strip() or stable_identity(
            "proof-idea-branch",
            self.theorem_name,
            self.cache_owner_theorem_name or self.theorem_name,
        )
        route = self.proof_graph.record_strategy_route(
            name=(
                f"mini_recursive_p{pass_index}_root_route"
                if pass_index is not None
                else "mini_recursive_root_route"
            ),
            description=(
                "Mini-recursive root assembly contract requiring the terminal "
                "claim's transitive dependency closure."
            ),
            route_key=":".join(
                str(item)
                for item in (
                    "mini_recursive",
                    "root_route",
                    pass_index if pass_index is not None else "pass",
                    text_hash(contract_instance_key),
                )
            ),
            score=0.6,
            phase="mini_recursive_route_contract",
            turn_index=turn_index,
            metadata={
                "route_scope": "root_assembly",
                "source_phase": "mini_recursive_route_contract",
                "pass_index": pass_index,
                "claims_planned": record.get("claims_planned"),
                "claims_selected": record.get("claims_selected"),
                "accepted_claims": contract_claims,
                "root_assembly_claim_names": sorted(root_assembly_claim_names),
                "satisfied_dependency_helpers": satisfied_dependency_helpers,
                "contract_instance_key": contract_instance_key,
                "strategy": strategy_text,
                "strategy_lineage_id": strategy_lineage_id,
                "proof_idea_id": proof_idea_id,
                "branch_id": branch_id,
                "plan_notes": [
                    str(value or "").strip()
                    for value in list(record.get("plan_notes") or [])
                    if str(value or "").strip()
                ],
                "planner_deliberation": copy.deepcopy(deliberation),
                "root_statement_identity": root_statement_identity,
                "root_contract_identity": root_contract_identity,
                "root_contract_identity_statement_key": str(
                    record.get("root_contract_identity_statement_key")
                    if root_contract_identity
                    else ""
                ).strip(),
                "root_contract_identity_environment_hash": str(
                    record.get("root_contract_identity_environment_hash")
                    if root_contract_identity
                    else ""
                ).strip(),
                "root_contract_identity_evidence_receipt": str(
                    record.get("root_contract_identity_evidence_receipt")
                    if root_contract_identity
                    else ""
                ).strip(),
                "route_anchor_contracts": validated_route_anchor_contracts,
            },
        )
        for contract_claim in contract_claims:
            contract_claim["proof_idea_id"] = proof_idea_id
            contract_claim["root_route_id"] = route.node_id
            contract_claim["branch_id"] = branch_id
        route.metadata["accepted_claims"] = contract_claims
        route_envelope = ProofLineageEnvelope(
            proof_idea_id=proof_idea_id,
            strategy_lineage_id=strategy_lineage_id,
            route_id=route.node_id,
            statement_identity=root_statement_identity,
        )
        route.metadata.update(route_envelope.merged_metadata())
        self.proof_graph.set_route_assembly_contract(
            route.node_id,
            required_node_ids=required_node_ids,
            required_helper_names=required_helper_names,
            required_helper_source_hashes=required_helper_source_hashes,
            target_statement=self.root_statement,
            phase="mini_recursive_route_contract",
            turn_index=turn_index,
            metadata={
                "pass_index": pass_index,
                "accepted_claims": contract_claims,
                "root_assembly_claim_names": sorted(root_assembly_claim_names),
                "satisfied_dependency_helpers": satisfied_dependency_helpers,
                "contract_instance_key": contract_instance_key,
                "strategy_lineage_id": strategy_lineage_id,
                "proof_idea_id": proof_idea_id,
                "branch_id": branch_id,
                "root_contract_identity": root_contract_identity,
                "route_anchor_contracts": validated_route_anchor_contracts,
            },
        )
        contract_status = self.proof_graph.route_assembly_contract_status(
            route.node_id,
            mutate=False,
        )
        contract_verdict = str(contract_status.get("verdict") or "")
        if contract_verdict not in {
            "route_assembly_contract_ready",
            "route_assembly_contract_authoring_ready_missing_bridge",
            "route_assembly_contract_incomplete",
        }:
            self.proof_graph.retire_strategy_route(
                route.node_id,
                reason=str(
                    contract_status.get("verdict") or "invalid route contract"
                ),
                verdict="root_route_contract_rejected",
            )
            return {}
        deliberation_observations: List[ProofIdeaObservation] = []
        deliberation_provenance = {
            "route_id": route.node_id,
            "source_pass_index": int(deliberation.get("pass_index", 0) or 0),
            "source_trigger": str(deliberation.get("trigger") or ""),
            "source_model_id": str(deliberation.get("model_id") or ""),
            "source_helpers_seen": int(
                deliberation.get("helpers_seen", 0) or 0
            ),
            "source_reasoning_tokens": int(
                deliberation.get("reasoning_tokens", 0) or 0
            ),
            "source_visible_output": str(
                deliberation.get("assistant_content") or ""
            ),
        }
        deliberation_routes = tuple(deliberation.get("routes") or ())
        if deliberation_routes:
            summary = "Planner deliberation alternatives: " + "; ".join(
                deliberation_routes
            )
            deliberation_observations.append(
                ProofIdeaObservation(
                    observation_id=stable_identity(
                        "proof-idea-deliberation-alternatives",
                        proof_idea_id,
                        summary,
                    ),
                    kind="alternative",
                    summary=summary,
                    **deliberation_provenance,
                    branch_id=branch_id,
                    turn_index=turn_index,
                )
            )
        candidate_lemmas = tuple(deliberation.get("candidate_lemmas") or ())
        if candidate_lemmas:
            summary = "Planner deliberation candidate lemmas: " + "; ".join(
                candidate_lemmas
            )
            deliberation_observations.append(
                ProofIdeaObservation(
                    observation_id=stable_identity(
                        "proof-idea-deliberation-theorems",
                        proof_idea_id,
                        summary,
                    ),
                    kind="theorem_discovery",
                    summary=summary,
                    theorem_names=candidate_lemmas,
                    **deliberation_provenance,
                    branch_id=branch_id,
                    turn_index=turn_index,
                )
            )
        for field_name, label in (
            ("bottlenecks", "Planner deliberation bottlenecks"),
            ("falsification_targets", "Planner falsification targets"),
        ):
            values = tuple(deliberation.get(field_name) or ())
            if not values:
                continue
            summary = f"{label}: " + "; ".join(values)
            deliberation_observations.append(
                ProofIdeaObservation(
                    observation_id=stable_identity(
                        "proof-idea-deliberation-note",
                        proof_idea_id,
                        field_name,
                        summary,
                    ),
                    kind="note",
                    summary=summary,
                    **deliberation_provenance,
                    branch_id=branch_id,
                    turn_index=turn_index,
                )
            )
        deliberation_note = str(deliberation.get("notes") or "").strip()
        if deliberation_note:
            deliberation_observations.append(
                ProofIdeaObservation(
                    observation_id=stable_identity(
                        "proof-idea-deliberation-note",
                        proof_idea_id,
                        "notes",
                        deliberation_note,
                    ),
                    kind="note",
                    summary=deliberation_note,
                    **deliberation_provenance,
                    branch_id=branch_id,
                    turn_index=turn_index,
                )
            )
        claim_ids_by_name: Dict[str, List[str]] = {}
        for contract_claim in contract_claims:
            claim_ids_by_name.setdefault(
                str(contract_claim.get("name") or ""), []
            ).append(str(contract_claim.get("claim_node_id") or ""))
        claim_intents: List[ProofIdeaClaimIntent] = []
        for contract_claim in contract_claims:
            claim_id = str(contract_claim.get("claim_node_id") or "").strip()
            if not claim_id:
                continue
            dependency_claim_ids = tuple(
                ids[0]
                for label in list(contract_claim.get("dependencies") or [])
                for ids in [claim_ids_by_name.get(str(label or ""), [])]
                if len(ids) == 1 and ids[0]
            )
            alternative_statements = tuple(
                str(value.get("statement") or "").strip()
                for value in list(contract_claim.get("variants") or [])
                if isinstance(value, dict)
                and str(value.get("statement") or "").strip()
            )
            alternative_identities = tuple(
                structural_statement_identity(
                    statement,
                    contract_identity=str(value.get("contract_identity") or ""),
                    statement_key=canonical_dossier_statement_key(statement),
                )
                for value, statement in (
                    (value, str(value.get("statement") or "").strip())
                    for value in list(contract_claim.get("variants") or [])
                    if isinstance(value, dict)
                )
                if statement
            )
            claim_intents.append(
                ProofIdeaClaimIntent(
                    claim_id=claim_id,
                    statement_identity=str(
                        contract_claim.get("statement_identity") or ""
                    ),
                    statement=str(contract_claim.get("statement") or ""),
                    role=str(contract_claim.get("role") or ""),
                    rationale=str(contract_claim.get("rationale") or ""),
                    sanity_check=str(
                        contract_claim.get("sanity_check") or ""
                    ),
                    counting_classification=str(
                        contract_claim.get("counting_classification") or ""
                    ),
                    obligation_id=str(
                        contract_claim.get("obligation_id") or ""
                    ),
                    invariant_refs=tuple(
                        contract_claim.get("invariant_refs") or ()
                    ),
                    consumer_ids=(route.node_id,),
                    dependency_claim_ids=dependency_claim_ids,
                    dependency_labels=tuple(
                        contract_claim.get("dependencies") or ()
                    ),
                    alternative_statement_identities=alternative_identities,
                    alternative_statements=alternative_statements,
                )
            )
            claim_node = self.proof_graph.nodes.get(claim_id)
            if claim_node is not None:
                claim_node.metadata["branch_id"] = branch_id
                claim_lineage = ProofLineageEnvelope(
                    proof_idea_id=proof_idea_id,
                    strategy_lineage_id=strategy_lineage_id,
                    route_id=route.node_id,
                    claim_id=claim_id,
                    statement_identity=str(
                        contract_claim.get("statement_identity") or ""
                    ),
                )
                claim_node.metadata.update(
                    claim_lineage.merged_metadata(claim_node.metadata)
                )
        existing_idea = self.proof_ideas.get(proof_idea_id)
        lifecycle_observations: Tuple[ProofIdeaObservation, ...] = tuple(
            deliberation_observations
        )
        if existing_idea is not None:
            prior_claim_ids = {
                intent.claim_id for intent in existing_idea.claim_intents
            }
            new_claim_ids = sorted(
                intent.claim_id
                for intent in claim_intents
                if intent.claim_id not in prior_claim_ids
            )
            prior_notes = set(existing_idea.notes)
            new_notes = sorted(
                str(value or "").strip()
                for value in list(record.get("plan_notes") or [])
                if str(value or "").strip() not in prior_notes
            )
            delta_parts = []
            if route.node_id not in existing_idea.consumer_ids:
                delta_parts.append(f"new consumer route {route.node_id}")
            if new_claim_ids:
                delta_parts.append("new claims " + ", ".join(new_claim_ids))
            if new_notes:
                delta_parts.append("new planner notes " + "; ".join(new_notes))
            if delta_parts:
                lifecycle_observations += (
                    ProofIdeaObservation(
                        observation_id=stable_identity(
                            "proof-idea-route-delta",
                            proof_idea_id,
                            route.node_id,
                            *delta_parts,
                        ),
                        kind="evidence_delta",
                        summary="; ".join(delta_parts),
                        route_id=route.node_id,
                        branch_id=branch_id,
                        turn_index=turn_index,
                    ),
                )
        self.upsert_proof_idea(
            ProofIdeaRecord(
                theorem_name=self.theorem_name,
                root_statement_identity=root_statement_identity,
                strategy=idea_strategy,
                route_shape_identity=route_shape_identity,
                status_history=(
                    ProofIdeaStatusTransition.create(
                        proof_idea_id=proof_idea_id,
                        occurrence_key=route.node_id,
                        status="active",
                        authority="controller",
                        reason="root route contract accepted for scheduling",
                        turn_index=turn_index,
                        route_id=route.node_id,
                        branch_id=branch_id,
                    ),
                ),
                branch_provenance=(
                    ProofIdeaBranchProvenance(
                        branch_id=branch_id,
                        source="mini_recursive_route_contract",
                    ),
                ),
                proof_idea_id=proof_idea_id,
                notes=(
                    tuple(record.get("plan_notes") or ())
                    + ((deliberation_note,) if deliberation_note else ())
                ),
                consumer_ids=(route.node_id,),
                claim_intents=tuple(claim_intents),
                observations=lifecycle_observations,
            )
        )
        self.record_proof_lineage_event(
            event_type="strategy_route_declared",
            envelope=route_envelope,
            phase="mini_recursive_route_contract",
            verdict="root_route_contract_declared",
            evidence_hash=text_hash(contract_instance_key),
            details={
                "strategy": strategy_text,
                "required_node_ids": list(required_node_ids),
            },
        )
        return {"route_id": route.node_id, "branch_id": branch_id}

    def _retarget_mini_recursive_route_contract_claim(
        self,
        record: Dict[str, Any],
        claim_node_id: str,
        *,
        statement: str = "",
    ) -> None:
        """Retarget aggregate mini-recursive contracts after claim repair."""

        if self.proof_graph is None:
            return
        new_node_id = str(claim_node_id or "").strip()
        if not new_node_id:
            return
        pass_index = record.get("pass_index")
        claim_index = record.get("claim_index")
        claim_name = str(record.get("claim_name") or "").strip()
        helper_name = str(record.get("helper_name") or "").strip()
        match_name = claim_name or helper_name
        record_statement_key = _mini_recursive_contract_statement_key(statement)
        allow_statement_retarget = (
            _mini_recursive_record_allows_contract_statement_retarget(record)
        )
        for route in list(self.proof_graph.nodes_by_kind("strategy_route")):
            metadata = route.metadata if isinstance(route.metadata, dict) else {}
            if metadata.get("source_phase") != "mini_recursive_route_contract":
                continue
            if str(metadata.get("pass_index")) != str(pass_index):
                continue
            accepted_claims = list(metadata.get("accepted_claims") or [])
            if not accepted_claims:
                continue
            name_counts: Dict[str, int] = {}
            for raw_item in accepted_claims:
                if not isinstance(raw_item, dict):
                    continue
                item_name = str(raw_item.get("name") or "").strip()
                if item_name:
                    name_counts[item_name] = int(name_counts.get(item_name, 0) or 0) + 1
            updated_claims: List[Dict[str, Any]] = []
            route_changed = False
            for raw_item in accepted_claims:
                item = dict(raw_item) if isinstance(raw_item, dict) else {}
                item_name = str(item.get("name") or "").strip()
                item_selected_index = str(item.get("selected_index") or "").strip()
                claim_index_text = str(claim_index or "").strip()
                item_source_index = str(item.get("source_index") or "").strip()
                record_source_index = str(record.get("source_index") or "").strip()
                item_statement = str(item.get("statement") or "").strip()
                item_statement_key = str(item.get("statement_key") or "").strip()
                if not item_statement_key:
                    item_statement_key = _mini_recursive_contract_statement_key(
                        item_statement
                    )
                    if item_statement_key:
                        item["statement_key"] = item_statement_key
                if match_name and item_name and item_name != match_name:
                    updated_claims.append(item)
                    continue
                name_matches = bool(
                    not claim_index_text
                    and match_name
                    and item_name == match_name
                    and int(name_counts.get(item_name, 0) or 0) == 1
                )
                index_matches = bool(
                    claim_index_text and item_selected_index == claim_index_text
                )
                source_index_conflicts = bool(
                    record_source_index
                    and item_source_index
                    and item_source_index != record_source_index
                )
                if index_matches and source_index_conflicts:
                    index_matches = False
                if not (name_matches or index_matches):
                    updated_claims.append(item)
                    continue
                statement_identity_mismatch = bool(
                    record_statement_key
                    and item_statement_key
                    and record_statement_key != item_statement_key
                )
                if statement_identity_mismatch and not allow_statement_retarget:
                    updated_claims.append(item)
                    continue
                old_node_id = str(item.get("claim_node_id") or "").strip()
                if old_node_id and old_node_id != new_node_id:
                    retarget = getattr(
                        self.proof_graph,
                        "retarget_route_assembly_contract_requirement",
                        None,
                    )
                    if callable(retarget):
                        route_changed = bool(
                            retarget(
                                route.node_id,
                                old_node_id=old_node_id,
                                new_node_id=new_node_id,
                            )
                        ) or route_changed
                    item["retargeted_from_claim_node_id"] = old_node_id
                item["claim_node_id"] = new_node_id
                if statement:
                    old_statement = str(item.get("statement") or "").strip()
                    statement_key_changed = bool(
                        record_statement_key
                        and item_statement_key
                        and record_statement_key != item_statement_key
                    )
                    if old_statement and (
                        old_statement != statement or statement_key_changed
                    ):
                        item.setdefault("original_statement", old_statement)
                        if item_statement_key:
                            item.setdefault("original_statement_key", item_statement_key)
                        old_claim_key = str(item.get("claim_key") or "").strip()
                        if old_claim_key:
                            item.setdefault("original_claim_key", old_claim_key)
                        for stale_field in (
                            "contract_identity",
                            "contract_identity_statement_key",
                            "contract_identity_environment_hash",
                            "contract_identity_evidence_receipt",
                            "contract_route_relation_kind",
                            "contract_route_relation_anchor_identity",
                            "contract_route_relation_evidence_receipt",
                            "proof_lineage",
                            "structural_statement_identity",
                            "statement_identity",
                        ):
                            item.pop(stale_field, None)
                    item["statement"] = statement
                    if record_statement_key:
                        item["statement_key"] = record_statement_key
                    item["claim_key"] = _mini_recursive_claim_obligation_key(
                        pass_index=pass_index,
                        selected_index=item_selected_index or claim_index,
                        name=item_name or match_name,
                        statement=statement,
                    )
                    item["statement_identity"] = structural_statement_identity(
                        statement,
                        statement_key=record_statement_key,
                    )
                updated_claims.append(item)
            claims_changed = updated_claims != accepted_claims
            if claims_changed:
                metadata["accepted_claims"] = updated_claims
                contract = metadata.get("route_assembly_contract")
                if isinstance(contract, dict):
                    contract_metadata = contract.get("metadata")
                    if isinstance(contract_metadata, dict):
                        contract_metadata["accepted_claims"] = updated_claims
            if not route_changed:
                continue
            metadata["accepted_claims"] = updated_claims
            contract = metadata.get("route_assembly_contract")
            if isinstance(contract, dict):
                contract_metadata = contract.get("metadata")
                if isinstance(contract_metadata, dict):
                    contract_metadata["accepted_claims"] = updated_claims

    def _mini_recursive_route_contract_claim_context(
        self,
        record: Dict[str, Any],
    ) -> Dict[str, Any]:
        """Return the selected route-contract claim matching a claim event."""

        if self.proof_graph is None:
            return {}
        pass_index = record.get("pass_index")
        claim_index_text = str(record.get("claim_index") or "").strip()
        claim_name = str(record.get("claim_name") or "").strip()
        helper_name = str(record.get("helper_name") or "").strip()
        match_name = claim_name or helper_name
        record_source_index = str(record.get("source_index") or "").strip()
        record_statement_key = _mini_recursive_contract_statement_key(
            str(record.get("statement") or "")
        )
        allow_statement_retarget = (
            _mini_recursive_record_allows_contract_statement_retarget(record)
        )
        scored_matches: List[Tuple[int, str, Dict[str, Any]]] = []
        for route in list(self.proof_graph.nodes_by_kind("strategy_route")):
            metadata = route.metadata if isinstance(route.metadata, dict) else {}
            if metadata.get("source_phase") != "mini_recursive_route_contract":
                continue
            if str(metadata.get("pass_index")) != str(pass_index):
                continue
            for raw_item in list(metadata.get("accepted_claims") or []):
                if not isinstance(raw_item, dict):
                    continue
                item = dict(raw_item)
                item_name = str(item.get("name") or "").strip()
                item_selected_index = str(item.get("selected_index") or "").strip()
                item_source_index = str(item.get("source_index") or "").strip()
                item_statement = str(item.get("statement") or "").strip()
                item_statement_key = str(item.get("statement_key") or "").strip()
                if not item_statement_key:
                    item_statement_key = _mini_recursive_contract_statement_key(
                        item_statement
                    )
                    if item_statement_key:
                        item["statement_key"] = item_statement_key
                if match_name and item_name and item_name != match_name:
                    continue
                index_matches = bool(
                    claim_index_text and item_selected_index == claim_index_text
                )
                name_matches = bool(match_name and item_name == match_name)
                if claim_index_text and not index_matches:
                    continue
                if not claim_index_text and match_name and not name_matches:
                    continue
                if (
                    record_source_index
                    and item_source_index
                    and item_source_index != record_source_index
                ):
                    continue
                statement_identity_mismatch = bool(
                    record_statement_key
                    and item_statement_key
                    and record_statement_key != item_statement_key
                )
                if statement_identity_mismatch and not allow_statement_retarget:
                    continue
                if statement_identity_mismatch and allow_statement_retarget:
                    for stale_field in (
                        "contract_identity",
                        "contract_identity_statement_key",
                        "contract_identity_environment_hash",
                        "contract_identity_evidence_receipt",
                        "contract_route_relation_kind",
                        "contract_route_relation_anchor_identity",
                        "contract_route_relation_evidence_receipt",
                        "proof_lineage",
                        "structural_statement_identity",
                    ):
                        item.pop(stale_field, None)
                    repaired_statement = str(record.get("statement") or "").strip()
                    if repaired_statement:
                        item["statement"] = repaired_statement
                    if record_statement_key:
                        item["statement_key"] = record_statement_key
                    item["statement_identity"] = structural_statement_identity(
                        repaired_statement,
                        statement_key=record_statement_key,
                    )
                score = 0
                if name_matches:
                    score += 16
                if index_matches:
                    score += 8
                if record_source_index and item_source_index == record_source_index:
                    score += 4
                if record_statement_key and item_statement_key == record_statement_key:
                    score += 2
                scored_matches.append((score, route.node_id, item))
        if not scored_matches:
            return {}
        scored_matches.sort(key=lambda entry: (entry[0], entry[1]), reverse=True)
        best_score = scored_matches[0][0]
        best = [item for item in scored_matches if item[0] == best_score]
        if len(best) == 1:
            return best[0][2]
        return {}

    def _record_mini_recursive_graph_native_event(
        self,
        record: Dict[str, Any],
    ) -> Dict[str, str]:
        """Project mini-recursive claim telemetry into graph-native search nodes."""

        if self.proof_graph is None:
            return {}
        phase = str(record.get("phase", "") or "")
        if phase not in {
            "mini_recursive_claim",
            "mini_recursive_claim_variant",
            "mini_recursive_claim_dependency",
            "mini_recursive_claim_typecheck",
            "mini_recursive_claim_sample",
            "mini_recursive_claim_tactic",
            "mini_recursive_claim_llm",
            "mini_recursive_claim_invalidated",
            "mini_recursive_claim_reuse",
        }:
            return {}

        statement = str(record.get("statement", "") or "").strip()
        claim_name = str(record.get("claim_name", "") or "").strip()
        helper_name = str(record.get("helper_name", "") or "").strip()
        verdict = str(record.get("verdict", "") or "").strip()
        turn_index = int(record.get("turn_in_phase", record.get("turn_index", 0)) or 0)
        statement_environment_metadata = self.statement_environment_metadata()

        pass_index = record.get("pass_index")
        claim_index = record.get("claim_index")
        planned_claim = self._mini_recursive_route_contract_claim_context(record)
        if not statement and planned_claim:
            statement = str(planned_claim.get("statement") or "").strip()
            if not claim_name:
                claim_name = str(planned_claim.get("name") or "").strip()
        record_contract_evidence_present = (
            _mini_recursive_event_contract_evidence_present(record)
        )
        record_contract_identity = _bound_mini_recursive_event_contract_identity(
            record,
            statement=statement,
        )
        contract_source: Mapping[str, Any]
        if record_contract_identity:
            contract_source = record
        elif record_contract_evidence_present:
            contract_source = {}
        else:
            contract_source = planned_claim
        claim_contract_identity = str(
            record_contract_identity
            or contract_source.get("contract_identity")
            or ""
        ).strip()
        claim_contract_evidence = {
            key: str(
                contract_source.get(key)
                or ""
            ).strip()
            for key in (
                "contract_identity_statement_key",
                "contract_identity_environment_hash",
                "contract_identity_evidence_receipt",
            )
        }
        claim_statement_identity = structural_statement_identity(
            statement,
            contract_identity=claim_contract_identity,
            statement_key=canonical_dossier_statement_key(statement),
        )
        strategy_lineage_id = str(
            planned_claim.get("strategy_lineage_id")
            if planned_claim
            else ""
        ).strip()
        proof_idea_id = str(
            planned_claim.get("proof_idea_id") if planned_claim else ""
        ).strip()
        root_route_id = str(
            planned_claim.get("root_route_id") if planned_claim else ""
        ).strip()
        try:
            record_lineage = ProofLineageEnvelope.from_metadata(record)
        except (TypeError, ValueError):
            record_lineage = ProofLineageEnvelope()
        proof_idea_id = proof_idea_id or record_lineage.proof_idea_id
        root_route_id = root_route_id or record_lineage.route_id
        if not strategy_lineage_id:
            strategy_lineage_id = strategy_lineage_identity(
                theorem_name=self.theorem_name,
                root_statement_identity=structural_statement_identity(
                    self.root_statement,
                    statement_key=canonical_dossier_statement_key(
                        self.root_statement
                    ),
                ),
                strategy="mini_recursive_claim_route",
                pass_index=record.get("pass_index"),
            )
        active_target_statements = (
            self.active_root_equivalence_statements_for_current_frame()
        )
        counterexample_text = "\n".join(
            str(record.get(key, "") or "")
            for key in (
                "claim_name",
                "helper_name",
                "statement",
                "reason",
                "output",
                "giveup_match",
            )
        )
        keep_non_solution_counterexample_obligation = bool(
            not _root_is_solution_placeholder_equivalence(self.root_statement)
            and _SPECULATIVE_COUNTEREXAMPLE_TEXT_RE.search(counterexample_text)
            and not _COUNTEREXAMPLE_EXCLUSION_TEXT_RE.search(counterexample_text)
        )
        root_suppression = graph_root_equivalent_suppression_decision(
            statement,
            self.root_statement,
            active_target_statements=active_target_statements,
            keep_non_solution_counterexample_obligation=(
                keep_non_solution_counterexample_obligation
            ),
        )
        if root_suppression.suppress:
            self.increment_tool_metric(
                "mini_graph_root_equivalent_claims_suppressed",
                1,
            )
            if self.proof_graph is not None:
                self.proof_graph.record_attempt(
                    self.proof_graph.root_node_id,
                    phase=phase,
                    turn_index=turn_index,
                    proof="",
                    verdict="root_equivalent_graph_native_claim_suppressed",
                    error_type="root_equivalent_graph_native_claim",
                    metadata={
                        "claim_name": claim_name,
                        "helper_name": helper_name,
                        "pass_index": pass_index,
                        "claim_index": claim_index,
                        "statement": statement,
                    },
                )
            return {}
        claim_key = _mini_recursive_claim_obligation_key(
            pass_index=pass_index,
            selected_index=claim_index,
            name=claim_name or helper_name,
            statement=statement,
        )
        if not claim_key and planned_claim:
            claim_key = str(planned_claim.get("claim_key") or "").strip()
        proposal_generation_key = "\n".join(
            str(item)
            for item in (
                "mini_recursive_claim_generation",
                f"pass={pass_index if pass_index is not None else 'unknown'}",
                f"selected={str(claim_index or '').strip() or 'unknown'}",
                f"name={claim_name or helper_name or 'claim'}",
            )
        )
        if not statement and not (claim_name or helper_name) and phase != "mini_recursive_claim":
            return {}
        variant_index_raw = record.get("variant_index")
        try:
            variant_index = (
                int(variant_index_raw)
                if variant_index_raw is not None and str(variant_index_raw) != ""
                else None
            )
        except (TypeError, ValueError):
            variant_index = None
        route_key = ":".join(
            str(item)
            for item in (
                "mini_recursive",
                pass_index if pass_index is not None else "pass",
                claim_key or claim_index or "claim",
            )
            if str(item) != ""
        )
        route_name = "_".join(
            str(item)
            for item in (
                "mini_recursive",
                f"p{pass_index}" if pass_index is not None else "",
                claim_name
                or helper_name
                or (f"c{claim_index}" if claim_index else ""),
            )
            if str(item)
        )
        invalidated_parent_reason = (
            self.invalidated_statement_reason(statement) if statement else ""
        )
        invalidated_parent_route_poison = bool(
            invalidated_parent_reason
            and (
                phase == "mini_recursive_claim_dependency"
                or verdict == "claim_invalidated_by_child"
            )
        )
        missing_dependencies = sorted(
            {
                str(dep or "").strip()
                for dep in list(record.get("missing_dependencies") or [])
                if str(dep or "").strip()
            }
        )
        invalidated_parent_suppression_signature = ""
        if invalidated_parent_route_poison:
            invalidated_parent_suppression_signature = text_hash(
                "\n".join(
                    str(item)
                    for item in (
                        phase,
                        verdict,
                        pass_index,
                        claim_index,
                        variant_index if variant_index is not None else "",
                        claim_name,
                        helper_name,
                        canonical_dossier_statement_key(statement),
                        "|".join(missing_dependencies),
                    )
                )
            )
        existing_route_id = self.proof_graph.strategy_route_node_id(route_key)
        existing_route = self.proof_graph.nodes.get(existing_route_id)
        if (
            invalidated_parent_route_poison
            and existing_route is not None
            and existing_route.kind == "strategy_route"
            and bool(
                (existing_route.metadata or {}).get("route_retired")
                or (existing_route.metadata or {}).get("route_dependency_contradicted")
            )
        ):
            route_metadata = (
                existing_route.metadata if isinstance(existing_route.metadata, dict) else {}
            )
            seen_signatures = [
                str(item or "").strip()
                for item in list(
                    route_metadata.get(
                        "invalidated_parent_suppression_signatures"
                    )
                    or []
                )
                if str(item or "").strip()
            ]
            if (
                invalidated_parent_suppression_signature
                and invalidated_parent_suppression_signature in seen_signatures
            ):
                return {
                    "route_id": existing_route.node_id,
                    "skip_helper_attempt": "true",
                    "invalidated_parent_duplicate": "true",
                }
            if invalidated_parent_suppression_signature:
                route_metadata["invalidated_parent_suppression_signatures"] = (
                    seen_signatures + [invalidated_parent_suppression_signature]
                )
            if missing_dependencies:
                self.increment_tool_metric(
                    "mini_recursive_false_parent_dependency_work_suppressed",
                    len(missing_dependencies),
                )
            self.increment_tool_metric(
                "mini_recursive_invalidated_parent_events_suppressed",
                1,
            )
            return {
                "route_id": existing_route.node_id,
                "skip_helper_attempt": "true",
                "invalidated_parent_suppressed": "true",
            }
        route = self.proof_graph.record_strategy_route(
            name=route_name or "mini_recursive_route",
            description=(
                f"Mini-recursive route for {claim_name or helper_name or claim_key}"
            ),
            route_key=route_key,
            score=0.2,
            phase=phase,
            turn_index=turn_index,
            metadata={
                "route_scope": "partial_route",
                "pass_index": pass_index,
                "claim_index": claim_index,
                "claim_name": claim_name,
                "source_phase": phase,
                "strategy_lineage_id": strategy_lineage_id,
                "proof_idea_id": proof_idea_id,
                "parent_route_id": root_route_id,
            },
        )
        lifecycle_claim_id = self.register_proof_idea_consumer(
            proof_idea_id=proof_idea_id,
            route_id=route.node_id,
            claim_id=str(planned_claim.get("claim_node_id") or "").strip(),
            statement_identity=claim_statement_identity,
            branch_id=str(planned_claim.get("branch_id") or "").strip(),
            branch_source="mini_recursive_claim",
        )
        route_envelope = ProofLineageEnvelope(
            proof_idea_id=proof_idea_id,
            strategy_lineage_id=strategy_lineage_id,
            parent_lineage_id=(
                str(planned_claim.get("strategy_lineage_id") or "").strip()
                if planned_claim
                and str(planned_claim.get("strategy_lineage_id") or "").strip()
                != strategy_lineage_id
                else ""
            ),
            route_id=route.node_id,
            claim_id=lifecycle_claim_id,
            statement_identity=claim_statement_identity,
        )
        route.metadata.update(route_envelope.merged_metadata(route.metadata))
        if invalidated_parent_route_poison:
            retire_route = getattr(self.proof_graph, "retire_strategy_route", None)
            if callable(retire_route):
                retired = bool(
                    retire_route(
                        route.node_id,
                        reason=invalidated_parent_reason,
                        verdict="route_dependency_contradicted",
                    )
                )
                if retired:
                    self.increment_tool_metric(
                        "mini_recursive_false_parent_routes_poisoned",
                        1,
                    )
                    if invalidated_parent_suppression_signature:
                        route.metadata[
                            "invalidated_parent_suppression_signatures"
                        ] = [invalidated_parent_suppression_signature]
                else:
                    return {
                        "route_id": route.node_id,
                        "skip_helper_attempt": "true",
                    }
            if missing_dependencies:
                self.increment_tool_metric(
                    "mini_recursive_false_parent_dependency_work_suppressed",
                    len(missing_dependencies),
                )
            self.increment_tool_metric(
                "mini_recursive_invalidated_parent_events_suppressed",
                1,
            )
            self.proof_graph.record_attempt(
                route.node_id,
                phase=phase,
                turn_index=turn_index,
                proof="",
                verdict="invalidated_parent_route_poisoned",
                error_type="invalidated_parent_statement",
                metadata={
                    "reason": invalidated_parent_reason,
                    "claim_name": claim_name,
                    "helper_name": helper_name,
                    "statement": statement,
                    "missing_dependencies": missing_dependencies,
                },
            )
            result = {
                "route_id": route.node_id,
                "invalidated_parent_suppressed": "true",
            }
            if phase == "mini_recursive_claim_dependency":
                result["skip_helper_attempt"] = "true"
            return result

        claim = None
        if claim_key or statement:
            claim = self.proof_graph.record_proposed_claim(
                name=claim_name or helper_name,
                statement=statement,
                claim_key=claim_key or statement,
                route_id=route.node_id,
                phase=phase,
                turn_index=turn_index,
                score=0.2,
                metadata={
                    "pass_index": pass_index,
                    "claim_index": claim_index,
                    "claim_name": claim_name,
                    "helper_name": helper_name,
                    "contract_identity": claim_contract_identity,
                    **claim_contract_evidence,
                    "structural_statement_identity": claim_statement_identity,
                    "proposal_generation_key": proposal_generation_key,
                    "source_phase": phase,
                    **statement_environment_metadata,
                    "root_equivalent_graph_native_claim": (
                        root_suppression.root_equivalent
                    ),
                },
            )
            claim_statement_identity = structural_statement_identity(
                claim.statement,
                contract_identity=str(
                    claim.metadata.get("contract_identity") or ""
                ).strip(),
                statement_key=canonical_dossier_statement_key(claim.statement),
            )
            claim.metadata["structural_statement_identity"] = (
                claim_statement_identity
            )
            self._retarget_mini_recursive_route_contract_claim(
                record,
                claim.node_id,
                statement=claim.statement,
            )
            claim_envelope = route_envelope.updated(
                claim_id=lifecycle_claim_id or claim.node_id
            )
            claim.metadata.update(
                claim_envelope.merged_metadata(claim.metadata)
            )
            self.record_proof_lineage_event(
                event_type="strategy_spawned_claim",
                envelope=claim_envelope,
                phase=phase,
                verdict=verdict,
                evidence_hash=claim.source_hash,
                details={"claim_name": claim.name},
            )

        variant = None
        if statement and claim is not None:
            variant_key = helper_name or ":".join(
                str(item)
                for item in (
                    claim_key,
                    variant_index if variant_index is not None else "variant",
                    record.get("variant_mode") or record.get("mode") or "",
                    statement,
                )
                if str(item)
            )
            variant = self.proof_graph.record_formal_variant(
                claim_node_id=claim.node_id,
                claim_name=claim.name,
                statement=statement,
                variant_name=helper_name or claim.name,
                variant_key=variant_key,
                variant_index=variant_index,
                variant_mode=str(record.get("variant_mode") or record.get("mode") or ""),
                phase=phase,
                turn_index=turn_index,
                score=0.2,
                metadata={
                    "pass_index": pass_index,
                    "claim_index": claim_index,
                    "helper_name": helper_name,
                    "claim_name": claim_name,
                    "contract_identity": claim_contract_identity,
                    **claim_contract_evidence,
                    "structural_statement_identity": claim_statement_identity,
                    "source_phase": phase,
                    **statement_environment_metadata,
                    "root_equivalent_graph_native_claim": (
                        root_suppression.root_equivalent
                    ),
                },
            )
            variant_envelope = route_envelope.updated(
                claim_id=claim.node_id,
                statement_identity=claim_statement_identity,
            )
            variant.metadata.update(
                variant_envelope.merged_metadata(variant.metadata)
            )

        root_route_target_id = (
            variant.node_id
            if variant is not None
            else (claim.node_id if claim is not None else "")
        )
        if (
            root_route_target_id
            and (
                root_suppression.exact_root_statement
                or root_suppression.active_root_statement
            )
        ):
            set_contract = getattr(
                self.proof_graph,
                "set_route_assembly_contract",
                None,
            )
            if callable(set_contract):
                set_contract(
                    route.node_id,
                    required_node_ids=[root_route_target_id],
                    target_statement=self.root_statement,
                    phase=phase,
                    turn_index=turn_index,
                    metadata={
                        "source_phase": phase,
                        "pass_index": pass_index,
                        "claim_index": claim_index,
                        "claim_name": claim_name,
                        "helper_name": helper_name,
                        "matched_active_root_target": (
                            root_suppression.active_root_statement
                            and not root_suppression.exact_root_statement
                        ),
                    },
                )

        failure_reason = self._mini_recursive_failure_reason(record)
        invalid_or_noisy_failure = verdict in {
            "variant_type_rejected",
            "variant_skipped_context_free_raw",
            "claim_invalidated_by_child",
            "claim_skipped_previous_child_invalidation",
            "claim_skipped_repaired_previous_child_invalidation",
        }
        if invalid_or_noisy_failure and statement:
            noisy_targets = [variant]
            if (
                claim is not None
                and (
                    not graph_statement_is_executable(statement)
                    or verdict
                    in {
                        "variant_skipped_context_free_raw",
                        "claim_invalidated_by_child",
                        "claim_skipped_previous_child_invalidation",
                        "claim_skipped_repaired_previous_child_invalidation",
                    }
                )
            ):
                noisy_targets.append(claim)
            for noisy_node in noisy_targets:
                if noisy_node is None:
                    continue
                self.proof_graph.record_attempt(
                    noisy_node.node_id,
                    phase=phase,
                    turn_index=turn_index,
                    proof="",
                    verdict=verdict,
                    error_type=self._mini_recursive_failure_error_type(record),
                    metadata={
                        "reason": failure_reason,
                        "claim_name": claim_name,
                        "helper_name": helper_name,
                    },
                )
            return {
                "route_id": route.node_id,
                "claim_id": claim.node_id if claim is not None else "",
                "variant_id": variant.node_id if variant is not None else "",
            }
        speculative_counterexample_failure = (
            _mini_recursive_speculative_counterexample_failure(
                record,
                self.root_statement,
            )
        )
        if speculative_counterexample_failure and failure_reason:
            for target_node in (variant, claim):
                if target_node is None:
                    continue
                self.proof_graph.record_attempt(
                    target_node.node_id,
                    phase=phase,
                    turn_index=turn_index,
                    proof="",
                    verdict=verdict,
                    error_type=self._mini_recursive_failure_error_type(record),
                    metadata={
                        "reason": failure_reason,
                        "claim_name": claim_name,
                        "helper_name": helper_name,
                        "speculative_counterexample_obligation_quarantined": True,
                    },
                )
            return {
                "route_id": route.node_id,
                "claim_id": claim.node_id if claim is not None else "",
                "variant_id": variant.node_id if variant is not None else "",
            }

        obligation = None
        create_failure_obligation = bool(
            failure_reason
            and verdict != "claim_dependency_blocked"
            and graph_statement_is_executable(statement)
        )
        if create_failure_obligation:
            source_id = (
                variant.node_id
                if variant is not None
                else (claim.node_id if claim is not None else route.node_id)
            )
            obligation_statement = statement
            failed_claim_adjudication = verdict in {
                "tactic_rejected",
                "claim_llm_failed",
                "claim_exhausted",
                "variant_type_rejected",
                "variant_falsified_by_sample",
                "variant_skipped_context_free_raw",
            }
            failed_claim_metadata = {
                "uncertified_failed_claim": failed_claim_adjudication,
                "certified_fact": not failed_claim_adjudication,
                "contract_identity": claim_contract_identity,
                **claim_contract_evidence,
                "structural_statement_identity": claim_statement_identity,
                **statement_environment_metadata,
                "target_integrity_adjudication": failed_claim_adjudication,
                "allow_root_equivalent_target_integrity_adjudication": (
                    failed_claim_adjudication
                ),
                "formalization_required": failed_claim_adjudication,
                "materialization_required": failed_claim_adjudication,
                "obligation_trust": (
                    "uncertified_failed_recursive_claim_pending_adjudication"
                    if failed_claim_adjudication
                    else "certified_recursive_claim_obligation"
                ),
            }
            obligation = self.proof_graph.record_missing_obligation(
                statement=obligation_statement,
                reason=failure_reason,
                source_node_id=source_id,
                route_id=route.node_id,
                phase=phase,
                turn_index=turn_index,
                error_type=self._mini_recursive_failure_error_type(record),
                metadata={
                    "pass_index": pass_index,
                    "claim_index": claim_index,
                    "variant_index": variant_index,
                    "claim_name": claim_name,
                    "helper_name": helper_name,
                    "verdict": verdict,
                    **failed_claim_metadata,
                },
            )
            self.proof_graph.record_replan_item(
                source_node_id=source_id,
                route_id=route.node_id,
                obligation_id=obligation.node_id,
                reason=failure_reason,
                phase=phase,
                turn_index=turn_index,
                priority=self._mini_recursive_replan_priority(verdict),
                metadata={
                    "pass_index": pass_index,
                    "claim_index": claim_index,
                    "variant_index": variant_index,
                    "claim_name": claim_name,
                    "helper_name": helper_name,
                    "verdict": verdict,
                    "target_statement": obligation_statement,
                    **failed_claim_metadata,
                },
            )
            if failed_claim_adjudication:
                self.increment_tool_metric(
                    "mini_recursive_failed_claim_obligations_pending_adjudication",
                    1,
                )
        if failure_reason and claim is not None:
            self.proof_graph.record_attempt(
                claim.node_id,
                phase=phase,
                turn_index=turn_index,
                proof="",
                verdict=verdict,
                error_type=self._mini_recursive_failure_error_type(record),
                metadata={
                    "reason": failure_reason,
                    "claim_name": claim_name,
                    "helper_name": helper_name,
                    "non_repairable_graph_native_failure": True,
                },
            )

        for dependency in list(record.get("missing_dependencies") or []):
            dep = str(dependency or "").strip()
            if not dep:
                continue
            dep_statement, dep_status = _mini_recursive_dependency_statement(
                self.proof_graph,
                dep,
                pass_index=pass_index,
                ignore_node_ids={
                    node.node_id
                    for node in (claim, variant)
                    if node is not None
                },
            )
            if not dep_statement:
                for blocked_node in (claim, variant):
                    if blocked_node is None:
                        continue
                    self.proof_graph.record_attempt(
                        blocked_node.node_id,
                        phase="mini_recursive_dependency_unresolved",
                        turn_index=turn_index,
                        proof="",
                        verdict=(
                            "claim_invalidated_by_child"
                            if dep_status == "invalidated"
                            else "claim_dependency_blocked"
                        ),
                        error_type=f"dependency_{dep_status}",
                        metadata={
                            "missing_dependency": dep,
                            "dependency_status": dep_status,
                            "claim_name": claim_name,
                            "helper_name": helper_name,
                        },
                    )
                continue
            obligation = self.proof_graph.record_missing_obligation(
                statement=dep_statement,
                reason=f"missing dependency for {claim_name or helper_name or claim_key}",
                source_node_id=claim.node_id if claim is not None else route.node_id,
                route_id=route.node_id,
                phase=phase,
                turn_index=turn_index,
                error_type="unproved_dependency",
                metadata={
                    "missing_dependency": dep,
                    "dependency_statement": dep_statement,
                    "dependency_resolution": dep_status,
                    "claim_name": claim_name,
                    "helper_name": helper_name,
                    "verdict": verdict,
                    **statement_environment_metadata,
                },
            )
            for blocked_node in (claim, variant):
                if blocked_node is None:
                    continue
                self.proof_graph.add_edge(
                    blocked_node.node_id,
                    obligation.node_id,
                    "blocked_by",
                )
                blocked_node.metadata["blocked_by_missing_dependency"] = dep
                if blocked_node.status == "open":
                    blocked_node.status = "blocked"
            self.proof_graph.record_replan_item(
                source_node_id=claim.node_id if claim is not None else route.node_id,
                route_id=route.node_id,
                obligation_id=obligation.node_id,
                reason=f"prove missing dependency {dep}",
                phase=phase,
                turn_index=turn_index,
                priority=0.8,
                metadata={
                    "missing_dependency": dep,
                    "claim_name": claim_name,
                    "helper_name": helper_name,
                    "verdict": verdict,
                },
            )

        _resolve_graph_native_obligations_against_verified_helpers(self)

        return {
            "route_id": route.node_id,
            "claim_id": claim.node_id if claim is not None else "",
            "variant_id": variant.node_id if variant is not None else "",
        }

    @staticmethod
    def _mini_recursive_failure_error_type(record: Dict[str, Any]) -> str:
        verdict = str(record.get("verdict", "") or "")
        phase = str(record.get("phase", "") or "")
        if verdict == "variant_type_rejected":
            return "type_rejected"
        if verdict == "variant_falsified_by_sample":
            return "sample_falsified"
        if verdict == "claim_dependency_blocked":
            return "unproved_dependency"
        if verdict == "claim_invalidated_by_child":
            return "child_invalidated_claim"
        if verdict in {
            "claim_skipped_previous_child_invalidation",
            "claim_skipped_repaired_previous_child_invalidation",
        }:
            return "previous_child_invalidation"
        attempts = list(record.get("tactic_attempts") or [])
        if attempts and isinstance(attempts[0], dict):
            error_type = str(attempts[0].get("error_type", "") or "").strip()
            if error_type:
                return error_type
        return verdict or phase

    @classmethod
    def _mini_recursive_failure_reason(cls, record: Dict[str, Any]) -> str:
        verdict = str(record.get("verdict", "") or "")
        if verdict in {"variant_type_ok", "variant_type_inconclusive"}:
            return ""
        if verdict in {"variant_sample_inconclusive", "variant_sample_skipped_dangerous_nat_pow"}:
            return ""
        if verdict == "tactic_solved":
            return ""
        if verdict == "claim_llm_solved":
            return ""
        if verdict == "variant_skipped_context_free_raw":
            return "formal variant was skipped because it lost required context"
        if verdict == "variant_type_rejected":
            output = str(record.get("output", "") or "").strip()
            return "formal variant was type rejected" + (
                f": {output[:300]}" if output else ""
            )
        if verdict == "variant_falsified_by_sample":
            reason = str(record.get("reason", "") or "").strip()
            return "sample check refuted the variant" + (
                f": {reason[:300]}" if reason else ""
            )
        if verdict == "claim_dependency_blocked":
            missing = [
                str(item or "").strip()
                for item in list(record.get("missing_dependencies") or [])
                if str(item or "").strip()
            ]
            return "claim has unproved dependencies" + (
                f": {', '.join(missing)}" if missing else ""
            )
        if verdict in {
            "tactic_rejected",
            "claim_llm_failed",
            "claim_exhausted",
            "claim_invalidated_by_child",
            "claim_skipped_previous_child_invalidation",
            "claim_skipped_repaired_previous_child_invalidation",
        }:
            reason = str(
                record.get("invalid_reason")
                or record.get("giveup_match")
                or record.get("tactic_exit_reason")
                or record.get("output")
                or ""
            ).strip()
            return (verdict.replace("_", " ")) + (f": {reason[:300]}" if reason else "")
        return ""

    @staticmethod
    def _mini_recursive_replan_priority(verdict: str) -> float:
        if verdict == "claim_dependency_blocked":
            return 0.9
        if verdict in {"claim_invalidated_by_child", "variant_falsified_by_sample"}:
            return 0.8
        if verdict in {"variant_type_rejected", "variant_skipped_context_free_raw"}:
            return 0.7
        if verdict in {"claim_llm_failed", "tactic_rejected", "claim_exhausted"}:
            return 0.6
        return 0.5

    def render_context(
        self,
        *,
        max_helpers: Optional[int] = None,
        max_proposed_helpers: int = 8,
        max_accepted_stubs: int = 3,
        current_goal_statement: str = "",
        current_preamble: str = "",
        current_context_lemmas: Iterable[str] = (),
    ) -> str:
        """Render a compact model-facing state update.

        Verified helper bodies are never rendered, only their signatures.  The
        production default is deliberately lossless: every named fact exposed
        to the model must carry its proposition in the same snapshot.  Callers
        doing diagnostics may still request an explicit recency cap.
        """
        self._refresh_verified_helper_quality()
        answer_safety_kwargs = self._answer_safety_kwargs()
        redact_solution_refs = effective_solution_placeholder_suppression(
            suppress_solution_placeholders=self.suppress_solution_placeholders,
            opaque_mode=bool(self.opaque_mode),
            allow_official_answer_visibility=bool(
                self.allow_official_answer_visibility
            ),
            official_answer_payload_present=getattr(
                self, "official_answer_payload_present", None
            ),
        )
        lines: List[str] = ["Proof workbench snapshot:"]
        if self.final_proof_hash:
            lines.append(f"- root status: solved ({self.final_proof_hash})")
        else:
            lines.append("- root status: open")
        framed_active_root_targets: Optional[List[Dict[str, Any]]] = None
        if current_goal_statement and current_preamble:
            framed_active_root_targets = active_root_targets_for_frame(
                self,
                root_statement=self.root_statement or current_goal_statement,
                preamble=current_preamble,
                helper_blocks=self.verified_helper_blocks(),
                require_helper_context_hash_match=True,
            )
        active_root_context = self.render_active_root_target_context(
            active_root_targets=framed_active_root_targets
        )
        if active_root_context:
            lines.append(active_root_context)
        active_strategy_context = self.render_active_strategy_context()
        if active_strategy_context:
            lines.append(active_strategy_context)
        lines.append(
            "- Named-fact boundary: only verified helpers listed below may be "
            "cited as already-proved named facts. Do not cite hidden benchmark, "
            "parent-root, or closed-form evaluation lemmas unless their exact "
            "names are listed. This boundary is not the whole mathematical "
            "context: unavailable facts are work items, not blockers. "
            "Manufacture new bridge facts from Mathlib/preamble primitives as "
            "fully proved local lemmas, definitions, or closed local `have` "
            "steps. If a bridge attempt still fails, show the concrete Lean "
            "failure from that attempted local proof and state the smallest "
            "next local target; do not turn missing named facts into prose "
            "about context, availability, or future work."
        )

        all_helpers = [
            helper
            for helper in self.verified_helpers.values()
            if not is_answer_unsafe_helper_source(
                helper.source,
                **answer_safety_kwargs,
            )
            and self._verified_helper_context_visible(helper)
        ]
        suppressed_helpers = [
            helper
            for helper in self.verified_helpers.values()
            if not is_answer_unsafe_helper_source(
                helper.source,
                **answer_safety_kwargs,
            )
            and not self._verified_helper_context_visible(helper)
        ]
        helper_limit = (
            None if max_helpers is None else max(0, int(max_helpers or 0))
        )
        helpers = (
            all_helpers
            if helper_limit is None
            else (all_helpers[-helper_limit:] if helper_limit else [])
        )
        if all_helpers:
            lines.append("- verified helper lemmas supplied as named facts:")
            if len(all_helpers) > len(helpers):
                all_names = ", ".join(
                    f"`{_prompt_safe_helper_name(helper.name, redact_solution_refs=redact_solution_refs)}`"
                    for helper in all_helpers
                )
                lines.append(
                    f"  - all verified helper names ({len(all_helpers)}): {all_names}"
                )
            for helper in helpers:
                signature = helper_prompt_signature(
                    helper.source,
                    name=helper.name,
                    redact_solution_refs=redact_solution_refs,
                )
                display_name = _prompt_safe_helper_name(
                    helper.name,
                    redact_solution_refs=redact_solution_refs,
                )
                lines.append(f"  - `{display_name}`: `{signature}`")
        else:
            lines.append("- verified helper lemmas supplied as named facts: none")

        conditional_suppressed_helpers = [
            helper
            for helper in suppressed_helpers
            if str(getattr(helper, "render_policy", "") or "")
            == "advisory_requires_unproved_premise"
        ]
        non_constructive_suppressed_count = len(suppressed_helpers) - len(
            conditional_suppressed_helpers
        )
        if conditional_suppressed_helpers:
            lines.append(
                "- verified conditional reducers withheld from named-fact use: "
                f"{len(conditional_suppressed_helpers)} require unproved premises"
            )
            conditional_limit = 8 if helper_limit is None else helper_limit
            conditional_helpers = (
                conditional_suppressed_helpers[-conditional_limit:]
                if conditional_limit
                else []
            )
            for helper in conditional_helpers:
                signature = helper_prompt_signature(
                    helper.source,
                    name=helper.name,
                    redact_solution_refs=redact_solution_refs,
                )
                display_name = _prompt_safe_helper_name(
                    helper.name,
                    redact_solution_refs=redact_solution_refs,
                )
                open_premises = [
                    _prompt_safe_inline_text(
                        str(premise or ""),
                        limit=220,
                        redact_solution_refs=redact_solution_refs,
                    )
                    for premise in list(
                        getattr(helper, "open_premise_statements", []) or []
                    )
                    if str(premise or "").strip()
                ]
                premise_text = "; ".join(open_premises) or "unknown premise"
                lines.append(
                    f"  - `{display_name}`: `{signature}`; "
                    f"open premise(s): {premise_text}"
                )
        if non_constructive_suppressed_count:
            lines.append(
                "- verified non-constructive/refutation helpers withheld from "
                f"named-fact use: {non_constructive_suppressed_count}"
            )

        proposed = [
            helper
            for helper in self.proposed_helpers.values()
            if not is_answer_unsafe_helper_source(
                helper.source,
                **answer_safety_kwargs,
            )
            and not is_answer_unsafe_statement_text(
                helper.statement,
                **answer_safety_kwargs,
            )
        ][-max_proposed_helpers:]
        if proposed:
            lines.append(
                "- proposed helper targets (not yet Lean-verified; do not cite as facts):"
            )
            for helper in proposed:
                statement = _prompt_safe_inline_text(
                    helper.statement,
                    limit=320,
                    redact_solution_refs=redact_solution_refs,
                )
                if not statement:
                    continue
                display_name = _prompt_safe_helper_name(
                    helper.name,
                    redact_solution_refs=redact_solution_refs,
                )
                lines.append(f"  - `{display_name}`: `{statement}`")

        if self.proof_graph is not None:
            obligations = [
                node
                for node in self.proof_graph.nodes_by_kind("missing_obligation")
                if str(getattr(node, "status", "") or "") in {"open", "blocked", "rejected"}
            ][-max_proposed_helpers:]
            if obligations:
                lines.append(
                    "- manufactured missing-fact obligations (not facts; prove or replace):"
                )
                for node in obligations:
                    metadata = dict(getattr(node, "metadata", {}) or {})
                    statement = _prompt_safe_inline_text(
                        str(getattr(node, "statement", "") or ""),
                        limit=360,
                        redact_solution_refs=redact_solution_refs,
                    )
                    reason = _prompt_safe_inline_text(
                        str(metadata.get("reason") or ""),
                        limit=220,
                        redact_solution_refs=redact_solution_refs,
                    )
                    move = (
                        "formalize the smallest executable Lean proposition, "
                        "then prove or schedule it"
                        if metadata.get("formalization_required")
                        else "prove this as a named helper or replan to a precise Lean-checkable obligation"
                    )
                    if (
                        metadata.get("formalization_required")
                        and metadata.get("formalization_statement_pending")
                    ):
                        parent_target = _prompt_safe_inline_text(
                            str(
                                metadata.get("materialization_parent_statement")
                                or metadata.get(
                                    "formalization_bridge_parent_statement"
                                )
                                or metadata.get("parent_repair_target_statement")
                                or ""
                            ),
                            limit=360,
                            redact_solution_refs=redact_solution_refs,
                        )
                        lines.append(
                            f"  - bridge brief: `{statement or '(formal target not yet available)'}`; "
                            f"reason: {reason or 'recorded proof gap'}; required move: {move}"
                        )
                        if parent_target:
                            lines.append(
                                f"    parent target to support: `{parent_target}`"
                            )
                        forbidden_fragments = [
                            _prompt_safe_inline_text(
                                str(fragment or ""),
                                limit=120,
                                redact_solution_refs=redact_solution_refs,
                            )
                            for fragment in list(
                                metadata.get("forbidden_materialization_fragments")
                                or ()
                            )
                            if str(fragment or "").strip()
                        ]
                        if forbidden_fragments:
                            lines.append(
                                "    stale rejected fragment(s), not standalone targets: "
                                + ", ".join(
                                    f"`{item}`" for item in forbidden_fragments[:4]
                                )
                            )
                        rejected_candidates = [
                            item
                            for item in list(
                                metadata.get("rejected_formalization_candidates")
                                or ()
                            )
                            if isinstance(item, dict)
                        ][-2:]
                        for candidate in rejected_candidates:
                            candidate_statement = _prompt_safe_inline_text(
                                str(candidate.get("statement") or ""),
                                limit=260,
                                redact_solution_refs=redact_solution_refs,
                            )
                            candidate_reason = _prompt_safe_inline_text(
                                str(candidate.get("reason") or "rejected"),
                                limit=120,
                                redact_solution_refs=redact_solution_refs,
                            )
                            if candidate_statement:
                                lines.append(
                                    f"    rejected candidate: `{candidate_statement}`; reason: {candidate_reason}"
                                )
                    else:
                        lines.append(
                            f"  - statement: `{statement or '(formal target not yet available)'}`; "
                            f"reason: {reason or 'recorded proof gap'}; required move: {move}"
                        )

        if self.proof_graph is not None:
            graph_summary = self.proof_graph.summary()
            lines.append(
                "- proof graph: "
                f"{graph_summary['nodes']} node(s), "
                f"{graph_summary['edges']} edge(s), "
                f"{graph_summary['proved_helpers']} proved helper node(s), "
                f"{graph_summary['failed_helpers']} failed/rejected/blocked helper node(s)"
            )

        if self.attempts:
            recent = self.attempts[-3:]
            rendered = ", ".join(
                f"{item.verdict or 'attempt'}"
                + (f"/{item.error_type}" if item.error_type else "")
                for item in recent
            )
            lines.append(f"- recent attempt outcomes: {rendered}")

        normalized_current_goal = str(current_goal_statement or "").strip()
        current_goal_key = canonical_dossier_statement_key(
            normalized_current_goal
        )
        current_goal_hash = (
            text_hash(normalized_current_goal) if normalized_current_goal else ""
        )
        if self.scratch:
            scoped_scratch = [
                item
                for item in self.scratch
                if (
                    not current_goal_hash
                    or (
                        not str(getattr(item, "goal_key", "") or "")
                        and not str(getattr(item, "goal_hash", "") or "")
                    )
                    or (
                        bool(str(getattr(item, "goal_key", "") or ""))
                        and str(getattr(item, "goal_key", "") or "")
                        == current_goal_key
                    )
                    or (
                        not str(getattr(item, "goal_key", "") or "")
                        and str(getattr(item, "goal_hash", "") or "")
                        == current_goal_hash
                    )
                )
            ]
            rendered_by_label: Dict[str, List[str]] = {}
            for item in scoped_scratch[-3:]:
                if not item.summary:
                    continue
                rendered_item = (
                    ("ok" if item.ok else "fail")
                    + f": {_prompt_safe_lean_diagnostic_text(item.summary, limit=300, redact_solution_refs=redact_solution_refs)}"
                )
                names = [
                    _prompt_safe_helper_name(
                        str(name or ""),
                        redact_solution_refs=redact_solution_refs,
                    )
                    for name in list(
                        getattr(item, "referenced_names", []) or []
                    )
                    if str(name or "").strip()
                ]
                names = [
                    name
                    for name in names
                    if name and "_hidden_" not in name
                ]
                if names:
                    rendered_item += "; declaration routes tried: " + ", ".join(
                        f"`{name}`" for name in names[:8]
                    )
                item_label = str(
                    getattr(item, "source_label", "") or "try_lean"
                )
                rendered_by_label.setdefault(item_label, []).append(
                    rendered_item
                )
            for item_label in sorted(rendered_by_label):
                lines.append(
                    f"- recent {item_label} checks: "
                    + ", ".join(rendered_by_label[item_label])
                )

        accepted_stubs = []
        current_preamble_hash = text_hash(current_preamble)
        current_context_hash = text_hash(
            "\n".join(str(item or "") for item in list(current_context_lemmas or ()))
        )
        skipped_answer_unsafe_stubs = 0
        if current_goal_hash:
            matching_stubs = []
            for stub in list(self.accepted_proof_stubs or ()):
                if stub.goal_hash != current_goal_hash:
                    continue
                if stub.preamble_hash != current_preamble_hash:
                    continue
                if stub.context_hash != current_context_hash:
                    continue
                code = str(getattr(stub, "normalized_code", "") or "").strip()
                if not code:
                    continue
                if redact_solution_refs and _contains_solution_ref_for_prompt(code):
                    skipped_answer_unsafe_stubs += 1
                    continue
                snippet_lines = _prompt_safe_code_snippet(
                    code,
                    redact_solution_refs=redact_solution_refs,
                )
                if not snippet_lines:
                    continue
                matching_stubs.append((stub, snippet_lines))
            accepted_stubs = matching_stubs[-max_accepted_stubs:]
        if accepted_stubs:
            lines.append(
                "- recent accepted try_lean proof snippets for this goal (scratch-checked; adapt before using):"
            )
            for stub, snippet_lines in accepted_stubs:
                lines.append(
                    f"  - turn {stub.turn_index}, tool {stub.tool_call_index}, "
                    f"goal {stub.goal_hash}:"
                )
                for line in snippet_lines:
                    lines.append(f"    {line}")
        elif skipped_answer_unsafe_stubs:
            lines.append(
                "- recent accepted try_lean proof snippets for this goal: "
                "withheld because the recorded code references a hidden answer placeholder."
            )
        elif self.accepted_proof_stubs:
            lines.append(
                "- recent accepted try_lean proof snippets: retained, but code hidden until the current goal/preamble/context hash matches."
            )

        if self.decl_applications:
            recent_decl_apps = self.decl_applications[-3:]
            lines.append("- recent apply_decl_to_goal probes:")
            for item in recent_decl_apps:
                decl_name = _prompt_safe_inline_text(
                    item.decl_name or "<unknown>",
                    limit=160,
                    redact_solution_refs=redact_solution_refs,
                )
                if item.closed:
                    status = "closed"
                elif item.applicable:
                    status = f"partial/{item.remaining_goal_count} goal(s)"
                else:
                    status = (
                        "rejected/"
                        + _prompt_safe_inline_text(
                            item.error_kind or "no_match",
                            limit=120,
                            redact_solution_refs=redact_solution_refs,
                        )
                    )
                target = _prompt_safe_inline_text(
                    item.statement_preview or "",
                    limit=220,
                    redact_solution_refs=redact_solution_refs,
                )
                target_suffix = f" against `{target}`" if target else ""
                lines.append(f"  - `{decl_name}`: {status}{target_suffix}")
                proof_stub = str(getattr(item, "proof_stub", "") or "").strip()
                if item.applicable and proof_stub:
                    snippet_lines = _prompt_safe_code_snippet(
                        proof_stub,
                        limit=400,
                        redact_solution_refs=redact_solution_refs,
                    )
                    if snippet_lines:
                        lines.append("    proof stub:")
                        for line in snippet_lines:
                            lines.append(f"      {line}")
                if item.applicable and item.remaining_goals_preview:
                    rendered_goals = ", ".join(
                        _prompt_safe_lean_diagnostic_text(
                            goal,
                            limit=160,
                            redact_solution_refs=redact_solution_refs,
                        )
                        for goal in item.remaining_goals_preview[:3]
                        if str(goal or "").strip()
                    )
                    if rendered_goals:
                        lines.append(f"    remaining goals: {rendered_goals}")
                elif not item.applicable and item.decl_type:
                    decl_type = _prompt_safe_inline_text(
                        item.decl_type,
                        limit=220,
                        redact_solution_refs=redact_solution_refs,
                    )
                    if decl_type:
                        lines.append(f"    declaration type: `{decl_type}`")
                if not item.applicable and item.error_text:
                    if bool(getattr(item, "error_text_is_lean_diagnostic", True)):
                        error_text = _prompt_safe_lean_diagnostic_text(
                            item.error_text,
                            limit=220,
                            redact_solution_refs=redact_solution_refs,
                        )
                        label = "Lean output"
                    else:
                        error_text = _prompt_safe_inline_text(
                            item.error_text,
                            limit=220,
                            redact_solution_refs=redact_solution_refs,
                        )
                        label = "Error"
                    if error_text:
                        lines.append(f"    {label}: {error_text}")

        return "\n".join(lines)

    def to_record(self) -> Dict[str, Any]:
        self.reconcile_proof_attempt_lineage()
        self.reconcile_proof_idea_graph_statuses()
        graph_record = (
            self.proof_graph.clone().to_record()
            if self.proof_graph is not None
            else None
        )
        projection_shadow: Optional[Dict[str, Any]] = None
        if (
            str(self.graph_execution_projection_mode or "").strip().lower()
            == "shadow"
            and isinstance(graph_record, dict)
        ):
            from .graph_execution_projection import project_graph_execution_shadow

            report = project_graph_execution_shadow(
                graph_record,
                project_environment_hash=str(
                    self.graph_execution_project_environment_hash or ""
                ),
            )
            projection_shadow = {
                "schema_version": report.schema_version,
                "mode": "shadow",
                "input_graph_digest": report.input_graph_digest,
                "report_digest": report.report_digest,
                "project_environment_hash": report.project_environment_hash,
                "counts": dict(report.counts),
                "unique_required_node_ids": list(report.unique_required_node_ids),
                "dangling_required_node_ids": list(
                    report.dangling_required_node_ids
                ),
                "route_classifications": [
                    {
                        "route_id": item.route_id,
                        "activation_status": item.activation_status,
                        "lifecycle_status": item.lifecycle_status,
                        "classification": item.classification,
                        "projection_debt": item.projection_debt,
                        "obligation_count": len(item.obligations),
                        "work_item_count": len(item.work_items),
                    }
                    for item in report.route_results
                ],
            }
        return {
            "schema_version": 1,
            "theorem_name": self.theorem_name,
            "root_statement": self.root_statement,
            "root_statement_hash": text_hash(self.root_statement),
            "problem_text": self.problem_text,
            "cache_owner_theorem_name": self.cache_owner_theorem_name,
            "proof_cache_publish_enabled": bool(
                self.proof_cache_publish_enabled
            ),
            "suppress_solution_placeholders": bool(
                self.suppress_solution_placeholders
            ),
            "opaque_mode": bool(self.opaque_mode),
            "allow_official_answer_visibility": bool(
                self.allow_official_answer_visibility
            ),
            "official_answer_payload_present": (
                None
                if self.official_answer_payload_present is None
                else bool(self.official_answer_payload_present)
            ),
            "verified_helpers": [
                asdict(item) for item in self.verified_helpers.values()
            ],
            "superseded_verified_helper_hashes": {
                str(name): [str(value) for value in list(values or [])]
                for name, values in self.superseded_verified_helper_hashes.items()
            },
            "verified_helper_source_hash_history": {
                str(name): [str(value) for value in list(values or [])]
                for name, values in self.verified_helper_source_hash_history.items()
            },
            # Fix 1 follow-up (2026-05-22): persist the soft-alias map so
            # downstream consumers (summary.json analysis, replay, cached
            # dossier reload) can see that duplicate-statement helpers
            # were detected. Architect adversarial review's finding 1.6
            # confirmed this gap.
            "verified_helper_statement_aliases": dict(
                self.verified_helper_statement_aliases
            ),
            "verified_helper_progress_deltas": {
                str(name): asdict(delta)
                for name, delta in self.verified_helper_progress_deltas.items()
            },
            "proof_lineage_events": clone_json_value(
                self.proof_lineage_events,
                label="dossier proof lineage events",
            ),
            "proof_lineage_event_ids": sorted(self.proof_lineage_event_ids),
            "proof_ideas": {
                idea_id: record.to_record()
                for idea_id, record in sorted(self.proof_ideas.items())
            },
            "proof_idea_singleton_child_scope": bool(
                self.proof_idea_singleton_child_scope
            ),
            "semantic_fact_registry": clone_json_value(
                self.semantic_fact_registry,
                label="dossier semantic fact registry",
            ),
            "action_value_observations": clone_json_value(
                self.action_value_observations,
                label="dossier action value observations",
            ),
            "proposed_helpers": [
                asdict(item) for item in self.proposed_helpers.values()
            ],
            "attempts": [asdict(item) for item in self.attempts],
            "scratch": [
                asdict(item) for item in _bounded_scratch_records(self.scratch)
            ],
            "accepted_scratch_registry": self.accepted_scratch_registry(),
            "accepted_proof_stubs": [
                asdict(item) for item in self.accepted_proof_stubs
            ],
            "tool_metrics": dict(self.tool_metrics),
            "decl_applications": [
                asdict(item) for item in self.decl_applications
            ],
            "mini_recursive_runs": clone_json_value(
                self.mini_recursive_runs,
                label="dossier recursive runs",
            ),
            "mini_recursive_claim_helper_bindings": clone_json_value(
                self.mini_recursive_claim_helper_bindings,
                label="dossier recursive claim bindings",
            ),
            "mini_recursive_invalidated_statement_reasons": dict(
                self.mini_recursive_invalidated_statement_reasons
            ),
            "mini_recursive_invalidation_provenance": clone_json_value(
                self.mini_recursive_invalidation_provenance,
                label="dossier recursive invalidation provenance",
            ),
            "mini_authoritative_negations": clone_json_value(
                self.mini_authoritative_negations,
                label="dossier authoritative negations",
            ),
            "mini_falsification_ledger": clone_json_value(
                self.mini_falsification_ledger,
                label="dossier falsification ledger",
            ),
            "mini_falsification_cursors": clone_json_value(
                self.mini_falsification_cursors,
                label="dossier falsification cursors",
            ),
            "root_disproof_certificate": clone_json_value(
                self.root_disproof_certificate,
                label="dossier root disproof certificate",
            ),
            "mini_falsification_pending_certificates": clone_json_value(
                self.mini_falsification_pending_certificates,
                label="dossier pending falsification certificates",
            ),
            "mini_falsification_certificate_replay_dispositions": clone_json_value(
                self.mini_falsification_certificate_replay_dispositions,
                label="dossier falsification replay dispositions",
            ),
            "mini_falsification_trust_boundary_conflict_certificate_hashes": sorted(
                self.mini_falsification_trust_boundary_conflict_certificate_hashes
            ),
            "mini_recursive_exhausted_claim_keys": sorted(
                self.mini_recursive_exhausted_claim_keys
            ),
            "active_root_targets": clone_json_value(
                self.active_root_targets,
                label="dossier active root targets",
            ),
            "active_root_classification_preamble_hash": str(
                self.active_root_classification_preamble_hash or ""
            ),
            "parallel_sample_proof_states": clone_json_value(
                self.parallel_sample_proof_states,
                label="dossier parallel sample proof states",
            ),
            "parallel_sample_failures": clone_json_value(
                self.parallel_sample_failures,
                label="dossier parallel sample failures",
            ),
            "proof_state_record": (
                clone_json_value(
                    getattr(self, "proof_state_record"),
                    label="dossier proof-state record",
                )
                if hasattr(self, "proof_state_record")
                else None
            ),
            "final_proof": self.final_proof,
            "final_proof_hash": self.final_proof_hash,
            "final_replay_helpers": list(self.final_replay_helpers),
            "root_proof_certificate": clone_json_value(
                self.root_proof_certificate,
                label="dossier root proof certificate",
            ),
            "graph_execution_projection_mode": str(
                self.graph_execution_projection_mode or "off"
            ),
            "graph_execution_project_environment_hash": str(
                self.graph_execution_project_environment_hash or ""
            ),
            "current_lean_environment_hash": str(
                self.current_lean_environment_hash or ""
            ),
            "lean_environment_ancestor_hashes": clone_json_value(
                self.lean_environment_ancestor_hashes,
                label="dossier Lean environment ancestry",
            ),
            # Deliberately NOT pruned to the "reachable" set.  Reachability is
            # computed from the ancestry map, but the digest that matters most
            # is the one for a FUTURE edge's parent — an environment that is by
            # definition not yet in that map.  Pruning dropped exactly those,
            # and absent content fails open, so a shrink the guard had refused
            # was silently accepted after a round-trip.  Carrying the whole map
            # costs checkpoint bytes; dropping it costs the invariant.
            "lean_environment_content_digests": clone_json_value(
                self.lean_environment_content_digests,
                label="dossier Lean environment content digests",
            ),
            "verified_helper_eviction_generation": int(
                self.verified_helper_eviction_generation or 0
            ),
            "graph_execution_projection_shadow": projection_shadow,
            "proof_graph": graph_record,
        }

    def to_execution_record(self) -> Dict[str, Any]:
        """Return the run-private, lossless dossier checkpoint projection.

        ``to_record`` remains suitable for reporting/replay consumers whose
        inverse applies prompt-safety normalization. A search checkpoint must
        additionally retain raw execution-bearing diagnostics and proof stubs,
        because those fields participate in future scheduling decisions.
        """

        record = self.to_record()
        record["execution_schema_version"] = 1
        record["execution_decl_applications"] = [
            asdict(item) for item in self.decl_applications
        ]
        record["execution_parallel_sample_failures"] = clone_json_value(
            self.parallel_sample_failures,
            label="dossier execution parallel sample failures",
        )
        record["execution_root_proof_finalization_receipts"] = sorted(
            self._root_proof_finalization_receipts
        )
        return record

    @classmethod
    def from_execution_record(cls, record: Dict[str, Any]) -> "ProofDossier":
        """Rehydrate execution fields with conservative helper filtering."""

        return cls._from_execution_record(record, authority=None)

    @classmethod
    def _from_authenticated_execution_record(
        cls,
        record: Dict[str, Any],
    ) -> "ProofDossier":
        """Restore a record owned by authenticated checkpoint infrastructure."""

        return cls._from_execution_record(
            record,
            authority=_AUTHENTICATED_EXECUTION_RESTORE,
        )

    @classmethod
    def _from_execution_record(
        cls,
        record: Dict[str, Any],
        *,
        authority: object | None,
    ) -> "ProofDossier":
        trusted_execution_restore = authority is _AUTHENTICATED_EXECUTION_RESTORE

        data = clone_json_value(
            record,
            label="dossier execution restore record",
        )
        if int(data.get("execution_schema_version", 0) or 0) != 1:
            raise ValueError("unsupported proof-dossier execution checkpoint schema")
        dossier = cls._from_record(
            data,
            trusted_execution_restore=trusted_execution_restore,
        )
        dossier._root_proof_finalization_receipts = set()
        if trusted_execution_restore:
            raw_root_receipts = data.get(
                "execution_root_proof_finalization_receipts"
            )
            if raw_root_receipts is not None and not isinstance(
                raw_root_receipts,
                list,
            ):
                raise ValueError(
                    "dossier execution checkpoint has invalid root proof receipts"
                )
            expected_root_receipt = dossier.root_proof_finalization_receipt_hash()
            if (
                expected_root_receipt
                and (
                    raw_root_receipts is None
                    or expected_root_receipt
                    in {
                        str(item or "").strip()
                        for item in raw_root_receipts
                        if isinstance(item, str)
                    }
                )
            ):
                dossier._root_proof_finalization_receipts.add(
                    expected_root_receipt
                )
        raw_decl_applications = data.get("execution_decl_applications")
        if not isinstance(raw_decl_applications, list):
            raise ValueError("dossier execution checkpoint lacks decl applications")
        dossier.decl_applications = [
            DeclApplicationRecord(
                turn_index=int(raw.get("turn_index") or 0),
                tool_call_index=int(raw.get("tool_call_index") or 0),
                decl_name=str(raw.get("decl_name") or ""),
                statement_hash=str(raw.get("statement_hash") or ""),
                applicable=bool(raw.get("applicable")),
                closed=bool(raw.get("closed")),
                remaining_goal_count=int(raw.get("remaining_goal_count") or 0),
                proof_stub_hash=str(raw.get("proof_stub_hash") or ""),
                error_kind=str(raw.get("error_kind") or ""),
                statement_preview=str(raw.get("statement_preview") or ""),
                proof_stub=str(raw.get("proof_stub") or ""),
                remaining_goals_preview=[
                    str(item) for item in list(raw.get("remaining_goals_preview") or [])
                ],
                error_text=str(raw.get("error_text") or ""),
                error_text_is_lean_diagnostic=bool(
                    raw.get("error_text_is_lean_diagnostic", True)
                ),
                decl_type=str(raw.get("decl_type") or ""),
            )
            for raw in raw_decl_applications
            if isinstance(raw, dict)
        ]
        raw_failures = data.get("execution_parallel_sample_failures")
        if not isinstance(raw_failures, list):
            raise ValueError("dossier execution checkpoint lacks parallel failures")
        dossier.parallel_sample_failures = clone_json_value(
            raw_failures,
            label="dossier restored parallel sample failures",
        )
        return dossier

    @classmethod
    def from_record(cls, record: Dict[str, Any]) -> "ProofDossier":
        """Rehydrate an untrusted/report dossier with conservative filters."""

        return cls._from_record(record, trusted_execution_restore=False)

    @classmethod
    def _from_record(
        cls,
        record: Dict[str, Any],
        *,
        trusted_execution_restore: bool,
    ) -> "ProofDossier":
        """Rehydrate a dossier from ``to_record`` JSON-compatible data."""

        data = dict(record or {})
        if "schema_version" in data:
            try:
                schema_version = int(data.get("schema_version"))
            except (TypeError, ValueError) as exc:
                raise ValueError("invalid proof-dossier schema_version") from exc
            if schema_version != 1:
                raise ValueError(
                    f"unsupported proof-dossier schema_version={schema_version}; expected 1"
                )
        graph_record = data.get("proof_graph")
        proof_graph = (
            ProofGraph.from_record(
                graph_record,
                resolve_helper_matches=False,
            )
            if isinstance(graph_record, dict)
            else None
        )
        root_statement = str(
            data.get("root_statement")
            or (
                graph_record.get("root_statement")
                if isinstance(graph_record, dict)
                else ""
            )
            or getattr(proof_graph, "root_statement", "")
            or ""
        )
        opaque_mode = bool(data.get("opaque_mode", True))
        suppress_solution_placeholders = bool(
            data.get("suppress_solution_placeholders", True)
        )
        allow_official_answer_visibility = bool(
            data.get("allow_official_answer_visibility", False)
        )
        raw_official_answer_payload_present = data.get(
            "official_answer_payload_present",
            None,
        )
        official_answer_payload_present = (
            None
            if raw_official_answer_payload_present is None
            else bool(raw_official_answer_payload_present)
        )
        answer_safety_kwargs = {
            "suppress_solution_placeholders": suppress_solution_placeholders,
            "opaque_mode": opaque_mode,
            "allow_official_answer_visibility": allow_official_answer_visibility,
            "official_answer_payload_present": official_answer_payload_present,
        }
        verified_helpers: Dict[str, VerifiedHelper] = {}
        restored_contract_evidence_rejected = 0
        restored_verified_helper_integrity_rejected = 0
        rejected_verified_helper_names: Set[str] = set()
        for raw in list(data.get("verified_helpers") or []):
            if not isinstance(raw, dict):
                continue
            item = VerifiedHelper(
                name=str(raw.get("name") or ""),
                source=str(raw.get("source") or ""),
                source_hash=str(raw.get("source_hash") or ""),
                phase=str(raw.get("phase") or ""),
                turn_index=int(raw.get("turn_index") or 0),
                support_names=[
                    str(name or "").strip()
                    for name in list(raw.get("support_names") or [])
                    if str(name or "").strip()
                ],
                support_source_hashes={
                    str(name or "").strip(): str(source_hash or "").strip()
                    for name, source_hash in dict(
                        raw.get("support_source_hashes") or {}
                    ).items()
                    if str(name or "").strip()
                    and str(source_hash or "").strip()
                },
                replay_context_names=[
                    str(name or "").strip()
                    for name in list(raw.get("replay_context_names") or [])
                    if str(name or "").strip()
                ],
                replay_context_source_hashes={
                    str(name or "").strip(): str(source_hash or "").strip()
                    for name, source_hash in dict(
                        raw.get("replay_context_source_hashes") or {}
                    ).items()
                    if str(name or "").strip()
                    and str(source_hash or "").strip()
                },
                provenance_tags=[
                    str(tag or "").strip()
                    for tag in list(raw.get("provenance_tags") or [])
                    if str(tag or "").strip()
                ],
                visibility_policy=str(raw.get("visibility_policy") or "").strip(),
                verification_environment_hash=str(
                    raw.get("verification_environment_hash") or ""
                ),
                quality_tags=[
                    str(tag or "").strip()
                    for tag in list(raw.get("quality_tags") or [])
                    if str(tag or "").strip()
                ],
                open_premise_statement_keys=[
                    str(key or "").strip()
                    for key in list(raw.get("open_premise_statement_keys") or [])
                    if str(key or "").strip()
                ],
                open_premise_statements=[
                    str(statement or "").strip()
                    for statement in list(raw.get("open_premise_statements") or [])
                    if str(statement or "").strip()
                ],
                closed_open_premise_statements=[
                    str(statement or "").strip()
                    for statement in list(
                        raw.get("closed_open_premise_statements") or []
                    )
                    if str(statement or "").strip()
                ],
                render_policy=str(raw.get("render_policy") or ""),
                contract_identity=str(raw.get("contract_identity") or ""),
                contract_identity_statement_key=str(
                    raw.get("contract_identity_statement_key") or ""
                ),
                contract_identity_environment_hash=str(
                    raw.get("contract_identity_environment_hash") or ""
                ),
                contract_identity_evidence_receipt=str(
                    raw.get("contract_identity_evidence_receipt") or ""
                ),
                contract_display_statement=str(
                    raw.get("contract_display_statement") or ""
                ),
                contract_binder_sorts=[
                    str(item or "")
                    for item in list(raw.get("contract_binder_sorts") or [])
                    if str(item or "").strip()
                ],
                contract_proof_binder_types=[
                    str(item or "")
                    for item in list(
                        raw.get("contract_proof_binder_types") or []
                    )
                    if str(item or "").strip()
                ],
            )
            item_statement = helper_decl_statement(item.source)
            item_body = helper_decl_body(item.source)
            item_has_bound_lean_statement = bool(
                verified_helper_bound_contract_identity(item)
            )
            helper_graph_node = None
            if proof_graph is not None:
                helper_graph_node_id = str(
                    proof_graph.helper_name_to_node_id.get(item.name, "")
                    or ""
                ).strip()
                helper_graph_node = proof_graph.nodes.get(helper_graph_node_id)
            helper_graph_metadata = dict(
                getattr(helper_graph_node, "metadata", {}) or {}
            )
            admission_policy = (
                "official_answer_visible"
                if official_answer_visible_to_llm(
                    opaque_mode=opaque_mode,
                    allow_official_answer_visibility=(
                        allow_official_answer_visibility
                    ),
                    official_answer_payload_present=(
                        official_answer_payload_present
                    ),
                )
                else "solution_suppressed"
            )
            expected_answer_safety_receipt = graph_helper_answer_safety_receipt(
                source_hash=item.source_hash,
                source_digest=hashlib.sha256(
                    item.source.encode("utf-8", errors="replace")
                ).hexdigest(),
                statement_key=canonical_dossier_statement_key(item_statement),
                environment_hash=str(
                    item.verification_environment_hash or ""
                ).strip(),
                render_policy=str(item.render_policy or "").strip(),
                visibility_policy=str(item.visibility_policy or "").strip(),
                admission_policy=admission_policy,
            )
            item_has_graph_verification_receipt = bool(
                helper_graph_node is not None
                and str(getattr(helper_graph_node, "kind", "") or "")
                == "helper"
                and str(getattr(helper_graph_node, "status", "") or "")
                == "proved"
                and str(getattr(helper_graph_node, "source_hash", "") or "")
                == item.source_hash
                and str(getattr(helper_graph_node, "proof_hash", "") or "")
                == item.source_hash
                and str(
                    helper_graph_metadata.get("verified_helper_source") or ""
                )
                == item.source
                and str(
                    helper_graph_metadata.get("verified_helper_source_hash") or ""
                )
                == item.source_hash
                and str(
                    helper_graph_metadata.get(
                        "verified_helper_environment_hash"
                    )
                    or ""
                ).strip()
                == str(item.verification_environment_hash or "").strip()
                and str(
                    helper_graph_metadata.get(
                        "verified_helper_answer_safety_receipt"
                    )
                    or ""
                )
                == expected_answer_safety_receipt
            )
            # Private execution checkpoints are a lossless inverse of a live
            # dossier whose helpers already crossed the Lean acceptance
            # boundary. Do not reapply planner-oriented surface heuristics to
            # that authenticated graph receipt: valid Lean propositions may
            # contain ``if ... then ... else``, and completed tactic proofs may
            # use ``refine ... ?_`` followed by bullet closures. Report/public
            # records retain the conservative filters below. Sound admissions
            # (sorry/admit and an unresolved ``exact ?_``) remain rejected by
            # the validated-complete placeholder check itself.
            trusted_execution_helper = bool(
                trusted_execution_restore
                and item_has_graph_verification_receipt
            )
            if (
                item.name
                and helper_decl_name(item.source) == item.name
                and text_hash(item.source) == item.source_hash
                and item_statement
                and not graph_statement_non_theorem_reason(item_statement)
                and (
                    graph_statement_is_executable(item_statement)
                    or item_has_bound_lean_statement
                    or trusted_execution_helper
                )
                and item_body
                and not has_materialization_incompatible_placeholders(
                    item_body,
                    validated_complete=trusted_execution_helper,
                )
                and (
                    trusted_execution_helper
                    or not has_placeholder_tactics(item_body)
                )
                and not is_answer_unsafe_helper_source(
                    item.source,
                    **answer_safety_kwargs,
                )
                and not is_answer_unsafe_statement_text(
                    item_statement,
                    **answer_safety_kwargs,
                )
                and item_has_graph_verification_receipt
            ):
                if item.contract_identity and not verified_helper_bound_contract_identity(
                    item
                ):
                    item.contract_identity = ""
                    item.contract_identity_statement_key = ""
                    item.contract_identity_environment_hash = ""
                    item.contract_identity_evidence_receipt = ""
                    item.contract_display_statement = ""
                    item.contract_binder_sorts = []
                    item.contract_proof_binder_types = []
                    restored_contract_evidence_rejected += 1
                verified_helpers[item.name] = item
            else:
                rejected_name = str(raw.get("name") or "").strip()
                if rejected_name:
                    rejected_verified_helper_names.add(rejected_name)
                restored_verified_helper_integrity_rejected += 1
        proposed_helpers: Dict[str, ProposedHelper] = {}
        for raw in list(data.get("proposed_helpers") or []):
            if not isinstance(raw, dict):
                continue
            item = ProposedHelper(
                name=str(raw.get("name") or ""),
                statement=str(raw.get("statement") or ""),
                source=str(raw.get("source") or ""),
                source_hash=str(raw.get("source_hash") or ""),
                phase=str(raw.get("phase") or ""),
                turn_index=int(raw.get("turn_index") or 0),
                proposal_revision=max(1, int(raw.get("proposal_revision") or 1)),
                statement_environment_hash=str(
                    raw.get("statement_environment_hash") or ""
                ).strip(),
            )
            item_statement = str(item.statement or "").strip()
            if (
                item.name
                and item_statement
                and helper_decl_name(item.source) == item.name
                and helper_decl_statement(item.source)
                and graph_statement_key(helper_decl_statement(item.source))
                == graph_statement_key(item_statement)
                and not graph_statement_non_theorem_reason(item_statement)
                and not is_answer_unsafe_statement_text(
                    item.name,
                    **answer_safety_kwargs,
                )
                and not is_answer_unsafe_statement_text(
                    item.statement,
                    **answer_safety_kwargs,
                )
                and not is_answer_unsafe_helper_source(
                    item.source,
                    **answer_safety_kwargs,
                )
            ):
                proposed_helpers[item.name] = item
        superseded_verified_helper_hashes: Dict[str, List[str]] = {}
        raw_superseded = data.get("superseded_verified_helper_hashes") or {}
        if isinstance(raw_superseded, dict):
            for raw_name, raw_hashes in raw_superseded.items():
                name = str(raw_name or "").strip()
                hashes = [
                    str(value or "").strip()
                    for value in list(raw_hashes or [])
                    if str(value or "").strip()
                ]
                if name and hashes:
                    superseded_verified_helper_hashes[name] = hashes
        verified_helper_source_hash_history: Dict[str, List[str]] = {}
        raw_hash_history = data.get("verified_helper_source_hash_history") or {}
        if isinstance(raw_hash_history, dict):
            for raw_name, raw_hashes in raw_hash_history.items():
                name = str(raw_name or "").strip()
                hashes = [
                    str(value or "").strip()
                    for value in list(raw_hashes or [])
                    if str(value or "").strip()
                ]
                if name and hashes:
                    verified_helper_source_hash_history[name] = hashes
        proof_ideas: Dict[str, ProofIdeaRecord] = {}
        for raw_id, raw_record in dict(data.get("proof_ideas") or {}).items():
            idea_id = str(raw_id or "").strip()
            if not idea_id or not isinstance(raw_record, Mapping):
                continue
            try:
                idea = ProofIdeaRecord.from_record(raw_record)
            except (TypeError, ValueError):
                # Advisory memory is fail-closed at the checkpoint boundary:
                # malformed records are discarded and never reconstructed from
                # prose or promoted into graph authority.
                continue
            if idea.proof_idea_id == idea_id:
                proof_ideas[idea_id] = idea
        dossier = cls(
            theorem_name=str(data.get("theorem_name") or ""),
            root_statement=root_statement,
            problem_text=str(data.get("problem_text") or ""),
            cache_owner_theorem_name=str(
                data.get("cache_owner_theorem_name") or ""
            ),
            proof_cache_publish_enabled=bool(
                data.get("proof_cache_publish_enabled", True)
            ),
            verified_helpers=verified_helpers,
            superseded_verified_helper_hashes=superseded_verified_helper_hashes,
            verified_helper_source_hash_history=verified_helper_source_hash_history,
            # Fix 1 follow-up (2026-05-22): rehydrate the alias map from
            # persisted records. Older records pre-dating this field
            # produce an empty dict via the default_factory, which is
            # the safe no-op.
            verified_helper_statement_aliases={
                str(req or "").strip(): str(canonical or "").strip()
                for req, canonical in dict(
                    data.get("verified_helper_statement_aliases") or {}
                ).items()
                if str(req or "").strip() and str(canonical or "").strip()
            },
            verified_helper_progress_deltas={
                str(name or "").strip(): delta
                for name, raw in dict(
                    data.get("verified_helper_progress_deltas") or {}
                ).items()
                for delta in [_coerce_verified_helper_progress_delta(raw)]
                if str(name or "").strip() and delta is not None
            },
            proof_lineage_events=[
                copy.deepcopy(raw)
                for raw in list(data.get("proof_lineage_events") or [])
                if isinstance(raw, dict)
            ],
            proof_lineage_event_ids={
                str(item or "").strip()
                for item in list(data.get("proof_lineage_event_ids") or [])
                if str(item or "").strip()
            },
            proof_ideas=proof_ideas,
            proof_idea_singleton_child_scope=(
                data.get("proof_idea_singleton_child_scope")
                if isinstance(data.get("proof_idea_singleton_child_scope"), bool)
                else False
            ),
            semantic_fact_registry={
                str(key or "").strip(): copy.deepcopy(value)
                for key, value in dict(
                    data.get("semantic_fact_registry") or {}
                ).items()
                if str(key or "").strip() and isinstance(value, dict)
            },
            action_value_observations={
                str(key or "").strip(): {
                    str(metric or ""): float(value or 0.0)
                    for metric, value in dict(raw or {}).items()
                }
                for key, raw in dict(
                    data.get("action_value_observations") or {}
                ).items()
                if str(key or "").strip() and isinstance(raw, dict)
            },
            proposed_helpers=proposed_helpers,
            suppress_solution_placeholders=suppress_solution_placeholders,
            opaque_mode=opaque_mode,
            allow_official_answer_visibility=allow_official_answer_visibility,
            official_answer_payload_present=official_answer_payload_present,
            proof_graph=None,
            graph_execution_projection_mode=str(
                data.get("graph_execution_projection_mode")
                if "graph_execution_projection_mode" in data
                else "off"
            ),
            graph_execution_project_environment_hash=str(
                data.get("graph_execution_project_environment_hash") or ""
            ),
            current_lean_environment_hash=str(
                data.get("current_lean_environment_hash") or ""
            ),
            lean_environment_ancestor_hashes={
                str(child or "").strip(): [
                    str(ancestor or "").strip()
                    for ancestor in list(ancestors or [])
                    if str(ancestor or "").strip()
                ]
                for child, ancestors in dict(
                    data.get("lean_environment_ancestor_hashes") or {}
                ).items()
                if str(child or "").strip()
            },
            verified_helper_eviction_generation=int(
                data.get("verified_helper_eviction_generation") or 0
            ),
            lean_environment_content_digests={
                str(environment or "").strip(): [
                    str(digest or "").strip()
                    for digest in list(digests or [])
                    if str(digest or "").strip()
                ]
                for environment, digests in dict(
                    data.get("lean_environment_content_digests") or {}
                ).items()
                if str(environment or "").strip()
            },
            mini_recursive_exhausted_claim_keys={
                str(item)
                for item in list(
                    data.get("mini_recursive_exhausted_claim_keys") or []
                )
                if str(item)
            },
        )
        # A fact ID is shared by equivalent helper aliases, so retaining a
        # whole persisted receipt merely because one alias survived source
        # verification launders the removed alias's names, hashes, resolved
        # nodes, and route claims. Rebuild the receipt membership solely from
        # source-verified helpers. Graph-derived members are reconstructed
        # below against the restored graph.
        dossier._rebuild_semantic_fact_registry(preserve_history=False)
        # Rebuild aliases under current fact-key semantics even when no graph
        # is attached, so stale statement-only aliases cannot survive restore.
        dossier._refresh_verified_helper_statement_aliases()
        if proof_graph is not None:
            dossier.proof_graph = proof_graph
            dossier.proof_graph.theorem_name = dossier.theorem_name
            dossier.proof_graph.ensure_root(dossier.root_statement)
            # ``ProofDossier`` is intentionally constructed before the graph
            # is authenticated and attached. Reconcile frozen node ancestry
            # now, before any restored helper can be matched to graph claims.
            dossier._refresh_all_graph_node_environment_ancestry()
            for rejected_name in sorted(
                rejected_verified_helper_names - set(dossier.verified_helpers)
            ):
                dossier.proof_graph.remove_helper(rejected_name)
            ready_before = dossier._ready_route_ids()
            dossier._sync_legacy_helpers_to_graph()
            dossier._sync_proposed_helpers_to_graph()
            dossier.reconcile_verified_facts(
                trigger="dossier_restore",
                ready_before=ready_before,
            )
            dossier.proof_graph.repair_proved_claim_child_variant_tombstones()
        redact_solution_refs = effective_solution_placeholder_suppression(
            suppress_solution_placeholders=suppress_solution_placeholders,
            opaque_mode=opaque_mode,
            allow_official_answer_visibility=allow_official_answer_visibility,
            official_answer_payload_present=official_answer_payload_present,
        )
        dossier.attempts = [
            ProofAttemptRecord(
                phase=str(raw.get("phase") or ""),
                turn_index=int(raw.get("turn_index") or 0),
                proof_hash=str(raw.get("proof_hash") or ""),
                helper_names=[
                    str(name or "").strip()
                    for name in list(raw.get("helper_names") or [])
                    if str(name or "").strip()
                ],
                verdict=str(raw.get("verdict") or ""),
                error_type=str(raw.get("error_type") or ""),
            )
            for raw in list(data.get("attempts") or [])
            if isinstance(raw, dict)
        ]
        dossier.scratch = _bounded_scratch_records([
            ScratchRecord(
                turn_index=int(raw.get("turn_index") or 0),
                tool_call_index=int(raw.get("tool_call_index") or 0),
                ok=bool(raw.get("ok")),
                summary=str(raw.get("summary") or ""),
                code_hash=str(raw.get("code_hash") or ""),
                normalized_code=str(raw.get("normalized_code") or ""),
                goal_hash=str(raw.get("goal_hash") or ""),
                goal_key=str(raw.get("goal_key") or ""),
                referenced_names=[
                    safe_name
                    for raw_name in list(raw.get("referenced_names") or [])
                    for safe_name in [
                        _prompt_safe_helper_name(
                            str(raw_name or "").strip(),
                            redact_solution_refs=redact_solution_refs,
                        )
                    ]
                    if safe_name and "_hidden_" not in safe_name
                ][:16],
                source_label=str(raw.get("source_label") or "try_lean"),
            )
            for raw in list(data.get("scratch") or [])
            if isinstance(raw, dict)
        ])
        proof_stub_records = data.get("accepted_proof_stubs")
        if proof_stub_records is None:
            proof_stub_records = data.get("accepted_scratch_registry")
        dossier.accepted_proof_stubs = [
            AcceptedProofStub(
                turn_index=int(raw.get("turn_index") or 0),
                tool_call_index=int(raw.get("tool_call_index") or 0),
                goal_hash=str(raw.get("goal_hash") or ""),
                preamble_hash=str(raw.get("preamble_hash") or ""),
                context_hash=str(raw.get("context_hash") or ""),
                code_hash=str(raw.get("code_hash") or ""),
                normalized_code=str(raw.get("normalized_code") or ""),
            )
            for raw in list(proof_stub_records or [])
            if isinstance(raw, dict)
        ]
        dossier.tool_metrics = {
            str(key): int(value or 0)
            for key, value in dict(data.get("tool_metrics") or {}).items()
            if str(key)
        }
        dossier._compact_attempt_history()
        # Migrate pre-lifecycle checkpoints before any scheduler frontier can
        # seal graph-native claim IDs into a cognition packet.  This runs
        # after restoring metrics so the repair remains observable instead of
        # being overwritten by the checkpoint's older metric snapshot.
        dossier.reconcile_proof_idea_graph_consumers()
        if restored_contract_evidence_rejected:
            dossier.increment_tool_metric(
                "mini_verified_helper_restore_contract_evidence_rejected",
                restored_contract_evidence_rejected,
            )
        if restored_verified_helper_integrity_rejected:
            dossier.increment_tool_metric(
                "mini_verified_helper_restore_integrity_rejected",
                restored_verified_helper_integrity_rejected,
            )
        decl_applications: List[DeclApplicationRecord] = []
        for raw in list(data.get("decl_applications") or []):
            if not isinstance(raw, dict):
                continue
            error_kind = str(raw.get("error_kind") or "")
            raw_error_text = str(raw.get("error_text") or "")
            lean_diagnostic_error = bool(
                raw.get(
                    "error_text_is_lean_diagnostic",
                    _decl_application_error_is_lean_diagnostic(
                        error_kind,
                        raw_error_text,
                    ),
                )
            )
            raw_proof_stub = str(raw.get("proof_stub") or "")
            proof_stub = (
                ""
                if is_answer_unsafe_statement_text(
                    raw_proof_stub,
                    **answer_safety_kwargs,
                )
                else _prompt_safe_inline_text(
                    raw_proof_stub,
                    limit=1000,
                    redact_solution_refs=redact_solution_refs,
                    preserve_backtick_contents=True,
                )
            )
            decl_applications.append(
                DeclApplicationRecord(
                    turn_index=int(raw.get("turn_index") or 0),
                    tool_call_index=int(raw.get("tool_call_index") or 0),
                    decl_name=(
                        _prompt_safe_helper_name(
                            str(raw.get("decl_name") or ""),
                            redact_solution_refs=redact_solution_refs,
                        )
                        if str(raw.get("decl_name") or "").strip()
                        else ""
                    ),
                    statement_hash=str(raw.get("statement_hash") or ""),
                    applicable=bool(raw.get("applicable")),
                    closed=bool(raw.get("closed")) and bool(proof_stub),
                    remaining_goal_count=int(raw.get("remaining_goal_count") or 0),
                    proof_stub_hash=str(raw.get("proof_stub_hash") or ""),
                    error_kind=error_kind,
                    statement_preview=_prompt_safe_lean_diagnostic_text(
                        raw.get("statement_preview") or "",
                        limit=1000,
                        redact_solution_refs=redact_solution_refs,
                    ),
                    proof_stub=proof_stub,
                    remaining_goals_preview=[
                        _prompt_safe_lean_diagnostic_text(
                            goal,
                            limit=500,
                            redact_solution_refs=redact_solution_refs,
                        )
                        for goal in list(raw.get("remaining_goals_preview") or [])
                    ],
                    error_text=(
                        _prompt_safe_lean_diagnostic_text(
                            raw_error_text,
                            limit=500,
                            redact_solution_refs=redact_solution_refs,
                        )
                        if lean_diagnostic_error
                        else _prompt_safe_inline_text(
                            raw_error_text,
                            limit=500,
                            redact_solution_refs=redact_solution_refs,
                        )
                    ),
                    error_text_is_lean_diagnostic=lean_diagnostic_error,
                    decl_type=_prompt_safe_inline_text(
                        raw.get("decl_type") or "",
                        limit=500,
                        redact_solution_refs=redact_solution_refs,
                    ),
                )
            )
        dossier.decl_applications = decl_applications
        dossier.mini_recursive_runs = [
            dict(item)
            for item in list(data.get("mini_recursive_runs") or [])
            if isinstance(item, dict)
        ]
        dossier.mini_recursive_claim_helper_bindings = {
            str(claim_name): copy.deepcopy(dict(binding or {}))
            for claim_name, binding in dict(
                data.get("mini_recursive_claim_helper_bindings") or {}
            ).items()
            if str(claim_name) and isinstance(binding, dict)
        }
        from .mini_falsification import (
            authoritative_certificate_record_is_valid,
            falsification_report_record_is_valid,
        )

        dossier.mini_falsification_ledger = [
            copy.deepcopy(item)
            for item in list(data.get("mini_falsification_ledger") or [])
            if falsification_report_record_is_valid(item)
            and (
                str(item.get("target_kind") or "") != "root"
                or _statements_share_bound_lean_identity(
                    dossier,
                    _exact_statement_text(item.get("statement")),
                    dossier.root_statement,
                    str(dossier.current_lean_environment_hash or "").strip(),
                )
            )
        ]
        _sort_falsification_ledger_by_evidence_time(
            dossier.mini_falsification_ledger
        )
        # Reconstruct progress only from the validated, content-addressed
        # report ledger.  The denormalized cursor map is a checkpoint cache,
        # not independent evidence that a route was actually searched.
        dossier.mini_falsification_cursors = {}
        for report in dossier.mini_falsification_ledger:
            report_statement = str(report.get("statement") or "").strip()
            environment_hash = str(report.get("environment_hash") or "")
            if not report_statement or not re.fullmatch(
                r"[0-9a-f]{64}", environment_hash
            ):
                continue
            target_cursors = _falsification_cursor_target_entry(
                dossier,
                report_statement,
                falsification_environment_hash=environment_hash,
                create=True,
            )
            if target_cursors is None:
                continue
            for finding in report.get("findings") or ():
                if not isinstance(finding, dict):
                    continue
                engine = str(finding.get("engine") or "").strip()
                cursor = finding.get("cursor")
                if not isinstance(cursor, Mapping) or not (
                    _recipe_repair_cursor_matches_finding(finding, cursor)
                ):
                    continue
                _merge_falsification_cursor(
                    target_cursors,
                    engine=engine,
                    cursor=cursor,
                    # Solver no-hit state is advisory, not authenticated proof
                    # evidence. Re-run it once after each process resume.
                    mark_smt_resume_recheck=True,
                )
        # A serialized proof-shaped blob is not fresh Lean authority.  Valid,
        # report-linked certificates are quarantined below for explicit replay.
        dossier.root_disproof_certificate = None
        # Serialized authority is audit history only. Fresh Lean replay below
        # is the sole admission path in a resumed process.
        dossier.mini_authoritative_negations = {}
        dossier.record_active_root_targets(
            [
                dict(item)
                for item in list(data.get("active_root_targets") or [])
                if isinstance(item, dict)
            ]
        )
        dossier.active_root_classification_preamble_hash = str(
            data.get("active_root_classification_preamble_hash") or ""
        ).strip()
        dossier.parallel_sample_proof_states = [
            dict(item)
            for item in list(data.get("parallel_sample_proof_states") or [])
            if isinstance(item, dict)
        ]
        dossier.parallel_sample_failures = [
            dict(item)
            for item in list(data.get("parallel_sample_failures") or [])
            if isinstance(item, dict)
        ]
        proof_state_record = data.get("proof_state_record")
        if isinstance(proof_state_record, dict):
            dossier.proof_state_record = copy.deepcopy(proof_state_record)
        final_proof = data.get("final_proof")
        dossier.final_proof = str(final_proof) if final_proof is not None else None
        final_proof_hash = data.get("final_proof_hash")
        dossier.final_proof_hash = (
            str(final_proof_hash) if final_proof_hash is not None else None
        )
        dossier.final_replay_helpers = [
            str(item or "").strip()
            for item in list(data.get("final_replay_helpers") or [])
            if str(item or "").strip()
        ]
        root_certificate = data.get("root_proof_certificate")
        dossier.root_proof_certificate = (
            copy.deepcopy(root_certificate)
            if isinstance(root_certificate, dict)
            else None
        )
        if (
            trusted_execution_restore
            and isinstance(dossier.root_proof_certificate, dict)
            and "target_environment_hash" not in dossier.root_proof_certificate
        ):
            # Lossless migration for authenticated checkpoints created before
            # proof certificates carried an explicit environment binding.
            dossier.root_proof_certificate["target_environment_hash"] = str(
                dossier.current_lean_environment_hash or ""
            ).strip()
        raw_provenance = dict(
            data.get("mini_recursive_invalidation_provenance") or {}
        )
        pending_target_environment_by_certificate_hash: Dict[str, str] = {}
        for provenance in raw_provenance.values():
            if (
                not isinstance(provenance, dict)
                or str(provenance.get("kind") or "")
                != "fresh_lean_certificate"
            ):
                continue
            provenance_certificate = provenance.get("certificate")
            if not isinstance(provenance_certificate, dict):
                continue
            provenance_certificate_hash = str(
                provenance_certificate.get("certificate_hash") or ""
            ).strip()
            target_environment_hash = str(
                provenance.get("target_environment_hash") or ""
            ).strip()
            if provenance_certificate_hash and target_environment_hash:
                pending_target_environment_by_certificate_hash[
                    provenance_certificate_hash
                ] = target_environment_hash

        dossier.mini_falsification_pending_certificates = []
        pending_hashes: Set[str] = set()
        for report in dossier.mini_falsification_ledger:
            for finding in list(report.get("findings") or []):
                if not isinstance(finding, dict):
                    continue
                certificate = finding.get("certificate")
                certificate_hash = (
                    str(certificate.get("certificate_hash") or "")
                    if isinstance(certificate, dict)
                    else ""
                )
                if (
                    authoritative_certificate_record_is_valid(certificate)
                    and str(certificate.get("statement") or "").strip()
                    == str(report.get("statement") or "").strip()
                    and str(certificate.get("environment_hash") or "").strip()
                    == str(report.get("environment_hash") or "").strip()
                    and certificate_hash not in pending_hashes
                ):
                    dossier.mini_falsification_pending_certificates.append(
                        {
                            "certificate": copy.deepcopy(certificate),
                            "report_hash": str(report.get("report_hash") or ""),
                            "target_kind": str(report.get("target_kind") or "helper"),
                            # Audit linkage only: fresh replay is still required
                            # before this can become mathematical authority.
                            "target_environment_hash": (
                                pending_target_environment_by_certificate_hash.get(
                                    certificate_hash,
                                    "",
                                )
                            ),
                        }
                    )
                    pending_hashes.add(certificate_hash)
        ledger_certificate_hashes = {
            str(certificate.get("certificate_hash") or "")
            for report in dossier.mini_falsification_ledger
            for finding in report.get("findings") or ()
            if isinstance(finding, dict)
            for certificate in [finding.get("certificate")]
            if isinstance(certificate, dict)
        }
        dossier.mini_falsification_certificate_replay_dispositions = {}
        for disposition_id, disposition in dict(
            data.get("mini_falsification_certificate_replay_dispositions") or {}
        ).items():
            if not _certificate_replay_disposition_is_valid(disposition):
                continue
            certificate_hash = str(disposition.get("certificate_hash") or "")
            expected_id = _certificate_replay_disposition_id(
                certificate_hash,
                str(disposition.get("environment_hash") or ""),
                str(disposition.get("policy_hash") or ""),
            )
            if (
                str(disposition_id or "") != expected_id
                or certificate_hash not in ledger_certificate_hashes
            ):
                continue
            dossier.mini_falsification_certificate_replay_dispositions[
                expected_id
            ] = copy.deepcopy(disposition)
        dossier.mini_falsification_trust_boundary_conflict_certificate_hashes = {
            str(item)
            for item in list(
                data.get(
                    "mini_falsification_trust_boundary_conflict_certificate_hashes"
                )
                or []
            )
            if isinstance(item, str)
            and re.fullmatch(r"[0-9a-f]{64}", item)
            and item in ledger_certificate_hashes
        }
        restored_conflict_hashes = set(
            dossier.mini_falsification_trust_boundary_conflict_certificate_hashes
        )
        # A public/report round-trip is not an authority boundary: a caller
        # can edit a valid ledger, metric, and denormalized hash set together.
        # Only authenticated execution checkpoints restore the process-local
        # receipts minted while both mathematical sides were live.
        setattr(
            dossier,
            "_mini_falsification_trust_boundary_conflict_certificate_hashes",
            restored_conflict_hashes if trusted_execution_restore else set(),
        )
        if (
            trusted_execution_restore
            and restored_conflict_hashes
            and int(
                dossier.tool_metrics.get(
                    "mini_falsification_trust_boundary_conflicts",
                    0,
                )
                or 0
            )
            > 0
        ):
            # Authenticated search checkpoints may restore the typed terminal
            # marker. Public records retain the hashes as telemetry/pending
            # evidence but cannot mint live conflict authority.
            setattr(
                dossier,
                "session_failure_reason",
                "falsification_trust_boundary_conflict",
            )
            setattr(dossier, "session_failure_kind", "proof_disproof_conflict")
        dossier.mini_recursive_invalidated_statement_reasons = {}
        dossier.mini_recursive_invalidation_provenance = {}
        _release_unverified_falsification_tombstones(dossier)
        dossier.reconcile_invalidated_graph_targets()
        return dossier
