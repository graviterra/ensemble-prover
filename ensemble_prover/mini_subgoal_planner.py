"""Mini-prover subgoal planning helpers.

This module is deliberately small and orchestration-free.  It turns LLM
planning responses into structured candidate claims, compiles those claims
through the shared subgoal compiler, and renders prompt/summary text for a
caller that owns model I/O and Lean execution.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from typing import Iterable, Mapping, Optional, Sequence

from .subgoal_compiler import SubgoalVariant, build_subgoal_variants
from .utils import normalize_subgoal_statement


_FENCE_RE = re.compile(
    r"```(?:json|JSON|Json)?\s*(?P<body>.*?)```",
    re.DOTALL,
)
_IDENT_CHUNK_RE = re.compile(r"[A-Za-z0-9_']+")
_LEAN_RESERVED_NAMES = frozenset(
    {
        "by",
        "case",
        "def",
        "do",
        "else",
        "example",
        "for",
        "fun",
        "have",
        "if",
        "import",
        "in",
        "induction",
        "let",
        "match",
        "namespace",
        "open",
        "rec",
        "show",
        "structure",
        "then",
        "theorem",
        "where",
        "with",
    }
)
_CLAIM_LIST_KEYS = ("claims", "subgoals", "lemmas", "steps", "plan")
_STATEMENT_KEYS = ("statement", "claim", "subgoal", "goal", "lemma", "target")
# A leading Lean declaration keyword can never begin a proposition/type, so a
# normalized statement still starting with one means normalization did not fully
# recover a bare proposition (e.g. a type-less `theorem foo := by` strips to
# `theorem foo`, which would otherwise slip past the malformed-surface filter).
_DECL_HEAD_RESIDUE_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:noncomputable\s+|private\s+|protected\s+|unsafe\s+|scoped\s+|local\s+)*"
    r"(?:theorem|lemma|example|def|abbrev|instance|structure|inductive|class)\b"
)
_MATERIALIZED_SOLUTION_RE = re.compile(
    r"(^|\n)\s*(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma|axiom)\s+"
    r"[A-Za-z0-9_'.]*_solution\b[^\n]*(?::=|where\b)",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class MiniSubgoalClaim:
    """A planned Lean claim plus compiled context-closed variants."""

    name: str
    statement: str
    # Planner-declared graph role.  This is scheduling metadata only: callers
    # must still establish root equivalence and dependency safety structurally.
    role: str = ""
    rationale: str = ""
    invariant_refs: tuple[str, ...] = field(default_factory=tuple)
    sanity_check: str = ""
    # Machine-readable planner-quality disposition for ``sanity_check``.
    # Free-form prose and this self-reported status are diagnostic metadata,
    # never proof authority: missing, conflicting, or failed receipts do not
    # remove, taint, or reprioritize an executable Lean proposition. Formal
    # checking or certified falsification owns mathematical rejection. Empty
    # checks conventionally use ``not_applicable``.
    sanity_status: str = ""
    # Parser provenance for the machine sanity contract.  Claims decoded from
    # a fresh provider response are versioned here so an omitted disposition
    # cannot silently acquire legacy/programmatic semantics after compilation
    # or checkpointing.  Controller-created claims retain version 0 and are
    # governed by their separate construction contracts.
    sanity_contract_version: int = 0
    counting_classification: str = ""
    dependencies: tuple[str, ...] = field(default_factory=tuple)
    variants: tuple[SubgoalVariant, ...] = field(default_factory=tuple)
    source_index: int = 0
    # Immutable persistence identity. Planner labels and list positions are
    # presentation details; checkpoints, repair cursors, and suspension must
    # bind to the semantic obligation and the plan that introduced it.
    obligation_id: str = ""
    origin_plan_fingerprint: str = ""
    # Exact provider-receipt provenance. Unlike ``obligation_id``, which names
    # a semantic route and can recur in a later tranche, this binds the claim
    # to the immutable visible response that originally emitted it.
    planner_receipt_id: str = ""
    # Receipt-local membership proof. This distinguishes identical semantic
    # claims emitted by different visible planner responses and prevents a
    # persisted claim from being cross-linked to another valid receipt.
    planner_receipt_claim_id: str = ""
    # Controller-authenticated derivation from the receipted source claim.
    # This is populated only when bounded repair/root substitution changes the
    # executable statement; restart validation recomputes it from the parent
    # receipt/link, transformed statement, variants, and transformation kind.
    planner_transformation_receipt_id: str = ""
    dependency_semantic_identities: tuple[tuple[str, str], ...] = field(
        default_factory=tuple
    )
    # Lean-elaborated contract evidence. ``statement`` remains the exact model
    # source executed by child proving; display syntax is diagnostic only and
    # structural identity is computed before Lean delaboration.
    contract_identity: str = ""
    contract_identity_statement_key: str = ""
    contract_identity_environment_hash: str = ""
    contract_identity_evidence_receipt: str = ""
    # Lean-certified same-batch definitional connection to the root or an
    # active target.  The receipt binds this advisory route relation to the
    # claim's own evidence receipt, the anchor identity, environment, and
    # exact/profile relation kind; consumers must revalidate all fields.
    contract_route_relation_kind: str = ""
    contract_route_relation_anchor_identity: str = ""
    contract_route_relation_evidence_receipt: str = ""
    contract_display_statement: str = ""
    contract_binder_sorts: tuple[str, ...] = field(default_factory=tuple)
    contract_proof_binder_types: tuple[str, ...] = field(default_factory=tuple)
    contract_proof_binder_structural_hashes: tuple[str, ...] = field(
        default_factory=tuple
    )
    contract_conclusion_structural_hash: str = ""
    contract_telescope_evidence_receipt: str = ""
    # Advisory orchestration findings.  These never establish mathematical
    # invalidity: the recursive scheduler may lower their priority, but only
    # Lean elaboration/proof checking or a certified counterexample can retire
    # the claim as false.
    policy_risk_reasons: tuple[str, ...] = field(default_factory=tuple)
    # Recovery provenance. These flags never grant mathematical authority;
    # repaired/substituted statements still traverse Lean and every downstream
    # contract/answer-safety filter.
    contract_identity_repaired: bool = False
    root_assembly_statement_substituted: bool = False
    # Explicit provenance for controller-added schema obligations. Such claims
    # still receive no proof authority and traverse every ordinary safety,
    # elaboration, dependency, and Lean verification gate.
    controller_synthesized: bool = False
    controller_role_restored: bool = False
    # Source arbitration runs before Lean and therefore cannot soundly decide
    # whether two proposition surfaces are definitionally equal (for example
    # ``MyTrue``/``True``, ``Eq``/``=``, or notation/projection aliases).
    # Claims carried only by such an unrecognized route stay provisional until
    # the shared Lean contract analyzer either connects the route to the root
    # structurally or discards its whole route DAG.  This flag grants no proof
    # or scheduling authority by itself.
    source_arbitration_provisional: bool = False


@dataclass(frozen=True)
class MiniSubgoalPlan:
    """Structured mini-prover subgoal plan.

    ``answer_safe_preamble_used`` records whether the caller supplied an
    answer-safe preamble summary to the planner prompt.  Raw preambles and
    materialized ``*_solution`` definitions should never be routed through
    this module's model-facing prompt renderer.
    """

    root_statement: str
    claims: tuple[MiniSubgoalClaim, ...] = field(default_factory=tuple)
    strategy: str = ""
    notes: tuple[str, ...] = field(default_factory=tuple)
    raw_response: str = ""
    answer_safe_preamble_used: bool = False
    root_contract_identity: str = ""
    root_contract_identity_statement_key: str = ""
    root_contract_identity_environment_hash: str = ""
    root_contract_identity_evidence_receipt: str = ""
    root_contract_display_statement: str = ""
    root_contract_binder_sorts: tuple[str, ...] = field(default_factory=tuple)
    root_contract_proof_binder_types: tuple[str, ...] = field(default_factory=tuple)
    root_contract_proof_binder_structural_hashes: tuple[str, ...] = field(
        default_factory=tuple
    )
    root_contract_conclusion_structural_hash: str = ""
    root_contract_telescope_evidence_receipt: str = ""
    # Provider declaration of whether this bounded tranche completes the
    # decomposition.  Appended after the legacy fields so positional callers
    # keep their original constructor ABI. ``None`` preserves compatibility
    # with older planner responses. This is an orchestration request only:
    # ``True`` never grants root-route authority unless the post-filter,
    # dependency-closed frontier contains an executable root assembly.
    plan_complete: Optional[bool] = None


def sanitize_theorem_name(
    raw_name: object,
    *,
    prefix: str = "mini_subgoal",
    index: Optional[int] = None,
    max_length: int = 64,
) -> str:
    """Return a conservative ASCII Lean theorem identifier."""

    raw = str(raw_name or "").strip()
    pieces = _IDENT_CHUNK_RE.findall(raw)
    name = "_".join(pieces).strip("_")
    if not name:
        name = prefix
    if name[0].isdigit() or name in _LEAN_RESERVED_NAMES:
        name = f"{prefix}_{name}"
    name = re.sub(r"_+", "_", name)
    if max_length > 0 and len(name) > max_length:
        name = name[:max_length].rstrip("_") or prefix
    if index is not None:
        suffix = f"_{max(1, int(index))}"
        if max_length > 0 and len(name) + len(suffix) > max_length:
            name = name[: max(1, max_length - len(suffix))].rstrip("_") or prefix
        name = f"{name}{suffix}"
    return name


# Guards against an O(openers * n) blowup on adversarial/garbage input full of
# unbalanced ``{``/``[`` (each opener triggers a scan-to-EOF). Normal planner
# responses have a handful of openers and are well under the size cap.
_MAX_SUBSTRING_EXTRACTION_CHARS = 200_000
_MAX_SUBSTRING_OPENERS = 500
_MAX_CLAIM_ARRAY_OPENERS = 64
_CANDIDATE_CONTEXT_CHARS = 180
_NON_PLAN_CONTAINER_KEYS = frozenset(
    {
        "reference",
        "references",
        "citation",
        "citations",
        "problem",
        "prompt",
        "notes",
        "metadata",
        "meta",
        "schema",
        "example",
        "examples",
        "format",
        "template",
    }
)
# Candidate provenance classes, best-to-worst for selection:
#   "primary"  — the whole response and ``` ```json ``` fences (+ string-aware
#                repairs): the model's ACTUAL output, carrying strategy / notes /
#                root_statement.
#   "recovery" — reconstructions (truncation salvage, anchored claim-list
#                extraction): claims-only, used to recover a malformed /
#                truncated / buried plan when no primary candidate parses.
#   "fragment" — balanced ``{..}`` object substrings from arbitrary positions:
#                where embedded claim-list objects live. Bare array fragments and
#                single claim-like object fragments are deliberately excluded;
#                only whole/fenced arrays, leading claim-object arrays, or
#                key-attached claim-list arrays are accepted as claim arrays.
# A recovery/anchored wrapper or a mid-text fragment can therefore NEVER outrank
# the genuine parsed plan, and metadata (carried only by primary candidates) is
# preserved.


def _double_encoded_json_candidates(raw: str) -> list[str]:
    """Recover a plan the model double-encoded as a JSON string value.

    Some models (observed with deepseek-v4-flash) emit
    ``{"`json`": "<the real plan JSON as a string>"}`` — an intended ```json
    code fence rendered as an object key — or return the whole plan as one
    quoted JSON string.  The outer JSON parses cleanly but carries no recognized
    claim-list key, so the real claims are never seen and the planner is treated
    as empty.  Unwrap any string value (one level) that itself parses as a JSON
    object/array, plus the whole-response-is-a-JSON-string case, so the embedded
    plan can be tried as a recovery candidate.
    """

    out: list[str] = []
    text = str(raw or "").strip()
    if not text or text[0] not in "[{\"":
        return out
    try:
        outer = json.loads(text, strict=False)
    except (json.JSONDecodeError, ValueError):
        return out

    def consider(value: object) -> None:
        if not isinstance(value, str):
            return
        inner = value.strip()
        if len(inner) < 2 or inner[0] not in "[{":
            return
        try:
            parsed = json.loads(inner, strict=False)
        except (json.JSONDecodeError, ValueError):
            return
        if isinstance(parsed, (dict, list)) and inner not in out:
            out.append(inner)

    if isinstance(outer, str):
        consider(outer)
    elif isinstance(outer, dict):
        for value in outer.values():
            consider(value)
    return out


def _planner_candidates_with_provenance(text: str) -> list[tuple[str, str, int]]:
    """Candidate JSON payloads paired with their provenance class.

    Returns ``(candidate_text, kind, context_score)`` where ``kind`` is
    ``"primary"``, ``"recovery"`` or ``"fragment"`` (see module notes above).
    """

    raw = str(text or "")
    candidates: list[tuple[str, str, int]] = []
    seen: set[tuple[str, str, int]] = set()

    def add(candidate: str, kind: str, *, start: int = 0, end: int = 0) -> None:
        c = (candidate or "").strip()
        key = (c, kind, max(0, int(start or 0)))
        if c and key not in seen:
            seen.add(key)
            candidates.append(
                (
                    c,
                    kind,
                    _candidate_context_score(raw, start=start, end=end, candidate=c),
                )
            )

    def add_with_repairs(
        block: str,
        kind: str,
        *,
        start: int = 0,
        end: int = 0,
    ) -> None:
        add(block, kind, start=start, end=end)
        # comment-stripped, then additionally trailing-comma-stripped. Both are
        # string-aware so they never alter content inside JSON string values.
        no_comments = _strip_jsonish_comments(block)
        add(no_comments, kind, start=start, end=end)
        add(_strip_trailing_commas(no_comments), kind, start=start, end=end)

    # Primary: the model's actual output (whole response + fenced bodies).
    add_with_repairs(raw, "primary", start=0, end=len(raw))
    for match in _FENCE_RE.finditer(raw):
        add_with_repairs(
            match.group("body"),
            "primary",
            start=match.start("body"),
            end=match.end("body"),
        )

    # Recovery: truncation salvage + anchored extraction of COMPLETE claim-list
    # arrays. Both run regardless of the size guard so a real plan is still
    # recovered when it sits after many stray openers or in a very large
    # response, but they are bounded (``_claim_array_openers`` is key-validated
    # and capped). Recovery is claim-list-key aware: arbitrary sibling arrays
    # like ``notes`` or ``references`` are never promoted to claims merely
    # because they parse as JSON arrays.
    # Double-encoded plans: the real JSON delivered as a quoted string value
    # (e.g. under a `json` key). Unwrap it as a recovery candidate so its claims
    # can win over the claim-less outer object.
    for inner in _double_encoded_json_candidates(raw):
        add_with_repairs(inner, "recovery", start=0, end=0)
    salvaged = _salvage_truncated_claim_objects(raw)
    if salvaged:
        add_with_repairs(salvaged, "recovery", start=0, end=0)
    leading_claim_array = _leading_claim_object_array(raw)
    if leading_claim_array:
        lead = len(raw) - len(raw.lstrip())
        add_with_repairs(
            leading_claim_array,
            "recovery",
            start=lead,
            end=lead + len(leading_claim_array),
        )
    all_claim_openers = _claim_array_openers(raw)
    non_plan_claim_object_spans: list[tuple[int, int]] = []
    for _key, _idx, _depth, obj_start, path in all_claim_openers:
        if obj_start < 0 or not _claim_path_has_non_plan_container(path):
            continue
        obj_end = _balanced_json_end(raw, obj_start, "{", "}")
        if obj_end is None:
            continue
        non_plan_claim_object_spans.append((obj_start, obj_end))
    valid_claims_object_spans: list[tuple[int, int]] = []
    valid_claims_object_starts: set[int] = set()
    for key, idx, _depth, obj_start, path in all_claim_openers:
        if key != "claims" or obj_start < 0:
            continue
        if _claim_path_has_non_plan_container(path):
            continue
        arr_end = _balanced_json_end(raw, idx, "[", "]")
        if arr_end is None:
            continue
        if not _claim_array_has_jsonish_object_continuation(raw, arr_end):
            continue
        obj_end = _balanced_json_end(raw, obj_start, "{", "}")
        if obj_end is None:
            obj_end = len(raw) - 1
        valid_claims_object_starts.add(obj_start)
        valid_claims_object_spans.append((obj_start, obj_end))
    claim_openers: list[tuple[str, int, int, int]] = []
    for key, idx, depth, obj_start, path in all_claim_openers:
        if key not in _CLAIM_LIST_KEYS:
            continue
        if _claim_path_has_non_plan_container(path):
            continue
        if any(
            span_start != obj_start and span_start <= idx <= span_end
            for span_start, span_end in valid_claims_object_spans
        ):
            continue
        # Within one JSON object, canonical ``claims`` is authoritative. Alias
        # recoveries from that same object must not override explicit
        # ``claims: []`` or a shorter canonical claim list.
        if key != "claims" and obj_start in valid_claims_object_starts:
            continue
        arr_end = _balanced_json_end(raw, idx, "[", "]")
        if arr_end is None:
            continue
        obj_end = _balanced_json_end(raw, obj_start, "{", "}") if obj_start >= 0 else None
        if obj_end is None:
            continue
        claim_openers.append((key, idx, depth, arr_end))
    # Prefer the SHALLOWEST array per claim-list key: a nested ``claims`` (e.g.
    # ``"decomposition":{"claims":[...]}``) must not be recovered in preference
    # to the real top-level claim list for that key.
    if claim_openers:
        min_depth_by_key: dict[str, int] = {}
        for key, _idx, depth, _arr_end in claim_openers:
            min_depth_by_key[key] = min(depth, min_depth_by_key.get(key, depth))
        for key, idx, depth, arr_end in claim_openers:
            if depth != min_depth_by_key.get(key):
                continue
            add_with_repairs(
                "{" + json.dumps(key) + ": " + raw[idx : arr_end + 1] + "}",
                "recovery",
                start=idx,
                end=arr_end + 1,
            )

    # Fragments: balanced object substrings from arbitrary positions. Bounded to
    # avoid quadratic blowup on adversarial/garbage input. Array substrings are
    # not included here because top-level lists are valid only as whole/fenced
    # planner outputs, or when recovered via an accepted claim-list key above.
    if len(raw) <= _MAX_SUBSTRING_EXTRACTION_CHARS:
        seen_openers = 0
        for start, ch in enumerate(raw):
            if ch != "{":
                continue
            seen_openers += 1
            if seen_openers > _MAX_SUBSTRING_OPENERS:
                break
            if any(
                span_start <= start <= span_end
                for span_start, span_end in non_plan_claim_object_spans
            ):
                continue
            end = _balanced_json_end(raw, start, "{", "}")
            if end is not None:
                add_with_repairs(
                    raw[start : end + 1],
                    "fragment",
                    start=start,
                    end=end + 1,
                )
    return candidates


def extract_planner_json_candidates(text: str) -> list[str]:
    """Extract likely JSON object/array payloads from raw LLM text."""

    return [
        candidate
        for candidate, _kind, _score in _planner_candidates_with_provenance(text)
    ]


def _candidate_context_score(
    raw: str,
    *,
    start: int,
    end: int,
    candidate: str,
) -> int:
    """Score local prose cues around a candidate JSON block.

    LLMs often include schema/example JSON next to the real plan. Structural JSON
    alone cannot distinguish those when examples use plausible statements, but
    the surrounding labels usually can: "Actual plan" and "My plan" are strong
    positive cues, while "schema", "example", and "format" are negative cues.
    """

    text = str(raw or "")
    start = max(0, min(len(text), int(start or 0)))
    prefix = text[max(0, start - _CANDIDATE_CONTEXT_CHARS) : start].lower()
    positive_markers = (
        "actual plan",
        "actual decomposition",
        "actual json",
        "my plan",
        "here is my plan",
        "here is the plan",
        "the actual plan",
        "final plan",
    )
    negative_markers = (
        "schema",
        "example",
        "for instance",
        "format",
        "template",
        "reference",
        "illustration",
        "field only",
        "field description",
    )
    positive_idx = max((prefix.rfind(marker) for marker in positive_markers), default=-1)
    negative_idx = max((prefix.rfind(marker) for marker in negative_markers), default=-1)
    score = 0
    if positive_idx >= 0 and positive_idx >= negative_idx:
        score += 4
    elif negative_idx >= 0:
        score -= 4

    lead = len(text) - len(text.lstrip())
    if start <= lead and str(candidate or "").lstrip().startswith("["):
        score += 2
    return score


def _has_claim_list_key(data: object) -> bool:
    """True if ``data`` is an object that EXPLICITLY provides a claim-list key.

    Returns True even when the key's value is an empty list — the point is to
    distinguish an INTENTIONAL empty plan (e.g. ``{"claims": []}`` "no further
    decomposition") from a MIS-SHAPED response that simply has no claim-list key
    at the top level (e.g. the plan wrapped under an unrecognized key). The
    ``plan`` key counts only when it is not a bare strategy string.
    """

    return bool(_claim_list_key(data))


def _claim_list_key(data: object) -> str:
    """Return the first explicit top-level claim-list key, if any."""

    if not isinstance(data, Mapping):
        return ""
    for key in _CLAIM_LIST_KEYS:
        if key not in data:
            continue
        if key == "plan" and isinstance(data.get(key), str):
            continue
        return key
    return ""


def _claim_list_key_score(data: object) -> int:
    key = _claim_list_key(data)
    if key == "claims":
        return 5
    if key in {"subgoals", "lemmas"}:
        return 4
    if key == "steps":
        return 3
    if key == "plan":
        return 2
    return 1 if isinstance(data, list) else 0


def _claim_statement_is_placeholder(statement: str) -> bool:
    text = str(statement or "").strip()
    if not text:
        return True
    lowered = text.lower()
    placeholder_markers = (
        "placeholder",
        "<your",
        "<lean proposition",
        "lean proposition to prove",
        "proposition to prove",
        "<statement",
        "<claim",
        "your statement here",
        "statement here",
        "to be filled",
        "todo",
    )
    if any(marker in lowered for marker in placeholder_markers):
        return True
    return bool(text.startswith("<") and text.endswith(">"))


def parse_mini_subgoal_plan_response(raw_response: str) -> MiniSubgoalPlan:
    """Parse JSON or fenced JSON from an LLM planner response.

    The accepted JSON shape is intentionally permissive.  Top-level arrays are
    treated as claim lists; top-level objects may contain ``claims``,
    ``subgoals``, ``lemmas``, ``steps``, or ``plan``.
    """

    parse_errors: list[str] = []
    # Rank parsed candidates and take the max. CLASS is the load-bearing signal:
    # primary (the model's real output, carrying strategy/notes/root_statement) >
    # recovery (claims-only reconstruction: salvage / anchored) > fragment
    # (substring / embedded example). This is a hard invariant: a recovery/
    # anchored wrapper or a mid-text fragment can NEVER outrank the genuinely
    # parsed plan, and metadata is preserved in the common case because a parsing
    # primary always wins and carries it.
    #   - Among same-class candidates: prefer most claims, then EARLIEST in
    #     source. (A real plan is usually stated up front and is the most
    #     complete decomposition; trailing schema/reference echoes and embedded
    #     examples typically carry fewer / placeholder claims.)
    # Metadata richness is deliberately NOT used to rank candidates: adversarial
    # review showed it is not a reliable signal (a schema example/template can be
    # metadata-rich while the real plan is terse, OR vice versa), so using it
    # merely trades one mis-selection for another.
    #
    # Inherent residual (NOT structurally fixable here — only the surrounding
    # prose distinguishes them, which is out of scope): when a response contains
    # MULTIPLE claim-bearing JSON blocks (an example/template/schema-echo plus
    # the real plan), the real plan may appear first or last and carry more or
    # fewer claims than the distractor; class+count picks the larger/earlier.
    # The planner prompt requests a single JSON object, and the _request_plan
    # repair-retry re-asks for one clean object, which mitigates this in practice.
    # A secondary residual: a real plan reachable ONLY via recovery (truncated /
    # prose-prefixed, no parsing primary) loses strategy/notes/root_statement
    # (claims are still recovered).
    # TRUST TIER (max wins), then source-context cues, empty-plan metadata
    # preservation, real/placeholder claim counts, canonical-key score, then
    # earliest source position:
    #   4  primary WITH claims        — the model's real output, decisive
    #   3  recovery WITH claims       — claims recovered from a genuine claim-list
    #                                   key (salvage/anchored): trusted; beats a
    #                                   wrapped primary with no top-level claim key.
    #      primary/fragment, 0 claims but an EXPLICIT claim-list key present (e.g.
    #                                   {"claims":[]}) — an intentional "no
    #                                   decomposition" signal; alias recoveries
    #                                   in the same object/subtree are suppressed.
    #   1  fragment WITH claims       — an embedded claim-list object; no-key
    #                                   claim-like fragments are skipped so
    #                                   references/problem objects cannot fabricate
    #                                   phantom claims.
    #   0  everything else: a primary with NO claim-list key at all (mis-shaped /
    #                       plan wrapped under an unrecognized key, where the real
    #                       claims live in a recovery/fragment that should win),
    #                       and any 0-claim recovery/fragment.
    # Distilled from the adversarial audit: a real recovery beats a wrapped
    # primary (3>0); an INTENTIONAL empty primary plan beats sibling aliases by
    # same-object suppression and beats a phantom fragment (3>1); but a MIS-SHAPED
    # primary with no claim-list key does NOT bury the fragment/recovery that
    # actually holds the claims (0 < 1 and 0 < 3).
    def _trust_tier(kind: str, has_claims: bool, has_key: bool) -> int:
        if kind == "primary":
            if has_claims:
                return 4
            return 3 if has_key else 0
        if kind == "recovery":
            return 3 if has_claims or has_key else 0
        if kind == "fragment" and has_key and not has_claims:
            return 3
        return 1 if has_claims else 0  # fragment

    best_key: Optional[tuple[int, int, int, int, int, int, int, int, int]] = None
    best: Optional[
        tuple[
            tuple[MiniSubgoalClaim, ...],
            str,
            Sequence[str],
            str,
            Optional[bool],
        ]
    ] = None
    for order, (candidate, kind, context_score) in enumerate(
        _planner_candidates_with_provenance(raw_response)
    ):
        try:
            # strict=False: models occasionally emit literal control
            # characters (raw newlines/tabs) inside JSON string values —
            # observed live killing a valid 9.9K-char deepseek plan. They are
            # harmless in rationale/strategy text; statements are Lean-checked
            # downstream regardless.
            data = json.loads(candidate, strict=False)
        except json.JSONDecodeError as exc:
            parse_errors.append(str(exc))
            continue
        if kind == "fragment" and not _has_claim_list_key(data):
            continue
        try:
            claims_data, strategy, notes, root_statement = _plan_parts_from_json(
                data
            )
            plan_complete = _plan_completion_from_json(data)
        except Exception as exc:
            parse_errors.append(str(exc))
            continue
        claims_acc: list[MiniSubgoalClaim] = []
        for idx, item in enumerate(claims_data, start=1):
            try:
                claim = _coerce_claim(
                    item,
                    source_index=idx,
                    require_sanity_contract=True,
                )
            except Exception as exc:
                parse_errors.append(f"claim {idx}: {exc}")
                continue
            if claim is not None:
                claims_acc.append(claim)
        claims = tuple(claims_acc)
        if claims_data and not claims:
            parse_errors.append(
                "claim list contained no coercible Lean propositions"
            )
            continue
        placeholder_count = sum(
            1 for claim in claims if _claim_statement_is_placeholder(claim.statement)
        )
        real_claim_count = len(claims) - placeholder_count
        metadata_score = int(
            kind in {"primary", "fragment"}
            and not claims
            and _has_claim_list_key(data)
            and bool(strategy or notes or root_statement)
        )
        root_route_score = int(
            any(
                str(claim.role or "").strip().lower() == "root_assembly"
                and not _claim_statement_is_placeholder(claim.statement)
                for claim in claims
            )
        )
        key = (
            _trust_tier(kind, bool(claims), _has_claim_list_key(data)),
            context_score,
            root_route_score,
            metadata_score,
            real_claim_count,
            -placeholder_count,
            _claim_list_key_score(data),
            len(claims),
            -order,
        )
        if best_key is None or key > best_key:
            best_key = key
            best = (claims, strategy, notes, root_statement, plan_complete)

    if best is None:
        details = parse_errors[0] if parse_errors else "no JSON candidate found"
        raise ValueError(f"could not parse mini subgoal plan JSON: {details}")
    # NOTE: a candidate that parses but yields 0 claims (e.g. an explicit
    # ``{"claims": []}`` "no further decomposition" signal) is returned as an
    # empty plan rather than raised — the recursive driver intentionally handles
    # empty plans (continuation passes). The ``has_claims``-first selection above
    # already ensures that when claims DO exist anywhere (e.g. wrapped under an
    # unrecognized key), they are recovered instead of an empty primary winning.

    claims, strategy, notes, root_statement, plan_complete = best
    return MiniSubgoalPlan(
        root_statement=root_statement,
        claims=claims,
        strategy=strategy,
        notes=tuple(notes),
        raw_response=str(raw_response or ""),
        plan_complete=plan_complete,
    )


def compile_mini_subgoal_plan(
    raw_claims: object,
    *,
    root_statement: str,
    goal_state: object = None,
    strategy: str = "",
    notes: Sequence[str] = (),
    raw_response: str = "",
    plan_complete: Optional[bool] = None,
    answer_safe_preamble_used: bool = False,
    name_prefix: str = "mini_subgoal",
    max_prefix_chars: int = 600,
    max_variants: int = 4,
) -> MiniSubgoalPlan:
    """Compile raw claim payloads into a MiniSubgoalPlan.

    Each non-empty claim statement is passed to
    ``ensemble_prover.subgoal_compiler.build_subgoal_variants`` with the
    explicit ``root_statement`` and optional Lean goal state supplied by the
    caller.
    """

    root = str(root_statement or "").strip()
    raw_items = _claim_items(raw_claims)
    used_names: set[str] = set()
    named_claims: list[tuple[MiniSubgoalClaim, str]] = []
    dependency_aliases: dict[str, str] = {}
    claims: list[MiniSubgoalClaim] = []
    dropped_variant_names: list[str] = []
    dropped_root_assembly_names: list[str] = []

    # Reserve every claim's own sanitized name up front.  ``_unique_name``
    # disambiguates by appending ``_2``, which can collide with a LATER claim
    # that is literally called ``x_2``: the disambiguator steals that name, the
    # real ``x_2`` is pushed to ``x_2_2``, and a dependency written ``x_2``
    # then binds to the wrong mathematics while the intended claim becomes
    # unreachable by name.  Reserving first makes the disambiguator skip past
    # names that are genuinely spoken for.
    reserved_names: set[str] = set()
    for idx, item in enumerate(raw_items, start=1):
        probe = _coerce_claim(item, source_index=idx, name_prefix=name_prefix)
        if probe is None:
            continue
        reserved = sanitize_theorem_name(
            probe.name,
            prefix=name_prefix,
            index=None,
        )
        if reserved:
            reserved_names.add(reserved)

    ordinal_registrations: list[tuple[int, str]] = []
    ambiguous_alias_keys: set[str] = set()
    for idx, item in enumerate(raw_items, start=1):
        claim = _coerce_claim(item, source_index=idx, name_prefix=name_prefix)
        if claim is None:
            continue
        own_name = sanitize_theorem_name(
            claim.name,
            prefix=name_prefix,
            index=None,
        )
        # This claim's own reservation must not block it from taking its name.
        reserved_names.discard(own_name)
        name = _unique_name(
            own_name,
            used_names | reserved_names,
            fallback_index=idx,
            prefix=name_prefix,
        )
        used_names.add(name)
        named_claims.append((claim, name))
        ordinal_registrations.append((idx, name))
        # Phase 1: a claim's REAL name/alias must win over any ordinal alias,
        # so a dependency on a claim literally named ``claim_1`` attaches to it
        # rather than to whichever claim happens to be first.
        for alias in _dependency_alias_keys(claim.name, name):
            existing = dependency_aliases.get(alias)
            if existing is not None and existing != name:
                # Two DIFFERENT claims fold to one dependency key (the key is
                # case- and separator-insensitive, so ``Foo Bar`` and
                # ``foo_bar`` collide).  Silently keeping the first binds the
                # edge to arbitrary mathematics; record the ambiguity and drop
                # the key so the dependency stays unresolved instead.
                ambiguous_alias_keys.add(alias)
                continue
            dependency_aliases.setdefault(alias, name)
    for alias in ambiguous_alias_keys:
        dependency_aliases.pop(alias, None)

    # Phase 2: ordinal aliases (claim N / lemma N / cN / N) fill only the keys
    # no real name already claimed.
    for idx, name in ordinal_registrations:
        ordinal_aliases = (
            idx,
            f"claim {idx}",
            f"Claim {idx}",
            f"step {idx}",
            f"Step {idx}",
            f"lemma {idx}",
            f"Lemma {idx}",
            f"c{idx}",
        )
        for alias in _dependency_alias_keys(*ordinal_aliases):
            dependency_aliases.setdefault(alias, name)

    for claim, name in named_claims:
        dependencies = tuple(
            dict.fromkeys(
                dependency_aliases.get(_dependency_key(dep), str(dep).strip())
                for dep in claim.dependencies
                if str(dep).strip()
            )
        )
        # Recover a bare proposition from any declaration-wrapped surface the
        # model emitted: `theorem NAME : PROP := by …` -> `PROP` (binders folded
        # back into a leading `∀`). Without this, a mathematically correct claim
        # carrying a decl header/proof tail is dropped downstream by the
        # malformed-statement-surface filter. build_subgoal_variants already
        # normalizes internally, so this only makes the STORED statement
        # consistent with the variants (both bare) instead of one wrapped, one
        # not. Falls back to the raw text when normalization yields nothing OR
        # leaves declaration residue it could not fully strip (a type-less decl
        # head like `theorem foo := by` normalizes to `theorem foo`, which is not
        # a proposition and would slip past the malformed-surface filter); the
        # raw text keeps that fail-closed so the filter still rejects it.
        normalized_statement = normalize_subgoal_statement(claim.statement)
        if not normalized_statement or _DECL_HEAD_RESIDUE_RE.match(
            normalized_statement
        ):
            normalized_statement = claim.statement
        variants = tuple(
            build_subgoal_variants(
                normalized_statement,
                root_statement=root,
                goal_state=goal_state,
                max_prefix_chars=max_prefix_chars,
                max_variants=max_variants,
            )
        )
        if not variants:
            dropped_variant_names.append(name)
            if str(claim.role or "").strip().lower() == "root_assembly":
                dropped_root_assembly_names.append(name)
            continue
        claims.append(
            MiniSubgoalClaim(
                name=name,
                statement=normalized_statement,
                role=claim.role,
                rationale=claim.rationale,
                invariant_refs=claim.invariant_refs,
                sanity_check=claim.sanity_check,
                sanity_status=claim.sanity_status,
                sanity_contract_version=claim.sanity_contract_version,
                counting_classification=claim.counting_classification,
                dependencies=dependencies,
                variants=variants,
                source_index=claim.source_index,
                source_arbitration_provisional=bool(
                    claim.source_arbitration_provisional
                ),
            )
        )

    compiled_notes = [str(n).strip() for n in notes if str(n).strip()]
    if dropped_variant_names:
        compiled_notes.append(
            "compile dropped claim(s) with no contextual variants: "
            + ", ".join(dropped_variant_names)
        )
    if dropped_root_assembly_names:
        compiled_notes.append(
            "compile omitted declared root_assembly claim(s) with no "
            "contextual variants: "
            + ", ".join(dropped_root_assembly_names)
        )

    return MiniSubgoalPlan(
        root_statement=root,
        claims=tuple(claims),
        strategy=str(strategy or "").strip(),
        notes=tuple(compiled_notes),
        raw_response=str(raw_response or ""),
        plan_complete=plan_complete if isinstance(plan_complete, bool) else None,
        answer_safe_preamble_used=bool(answer_safe_preamble_used),
    )


def compile_parsed_mini_subgoal_plan(
    parsed_plan: MiniSubgoalPlan,
    *,
    root_statement: str,
    goal_state: object = None,
    answer_safe_preamble_used: bool = False,
    max_prefix_chars: int = 600,
    max_variants: int = 4,
) -> MiniSubgoalPlan:
    """Compile a parsed planner response against the live root/goal context."""

    return compile_mini_subgoal_plan(
        parsed_plan.claims,
        root_statement=root_statement,
        goal_state=goal_state,
        strategy=parsed_plan.strategy,
        notes=parsed_plan.notes,
        raw_response=parsed_plan.raw_response,
        plan_complete=parsed_plan.plan_complete,
        answer_safe_preamble_used=answer_safe_preamble_used,
        max_prefix_chars=max_prefix_chars,
        max_variants=max_variants,
    )


def render_mini_subgoal_planner_prompt(
    *,
    root_statement: str,
    goal_state: object = None,
    answer_safe_preamble_summary: str = "",
    max_claims: int = 16,
    suppress_solution_placeholders: bool = True,
    solution_placeholder_filter_active: object = None,
) -> str:
    """Render an answer-safe JSON-planning prompt.

    ``answer_safe_preamble_summary`` must be a sanitized summary only: helper
    names, imports, and public non-answer context are fine; raw preambles,
    materialized ``*_solution`` definitions, and hidden answer values are not.
    """

    _assert_answer_safe_preamble_summary(
        answer_safe_preamble_summary,
        suppress_solution_placeholders=suppress_solution_placeholders,
    )
    goal_block = _format_goal_state(goal_state)
    preamble_block = str(answer_safe_preamble_summary or "").strip()
    parts = [
        (
            "Decompose the root theorem into an atomic theorem DAG of "
            "Lean-checkable intermediate claims for the mini-prover."
        ),
        (
            "Each claim should expose one stable mathematical interface that "
            "removes a real bottleneck. Split claims that prove multiple facts "
            "or combine a construction with its consequences."
        ),
        (
            "Do not spend claims on generic library facts, weak bounds, "
            "near-restatements of the root, or locally easy facts unless the "
            "rationale explains exactly how the final root proof will use them."
        ),
        (
            "Order the claims as a dependency DAG: foundational leaves before "
            "the lemmas that consume them. Delay bookkeeping computations such "
            "as total sums, standard formula evaluations, or cleanup identities "
            "until after the bridge claims that make the root theorem collapse."
        ),
        (
            "Use dependencies truthfully: if a later claim uses a witness, "
            "object, notation setup, or lemma introduced by an earlier claim, "
            "include that earlier claim name in dependencies. Do not leave a "
            "bridge claim dependency-free when its rationale relies on an "
            "earlier setup claim."
        ),
        (
            "Every nonempty plan must end with one claim whose `role` is "
            "`root_assembly`. Its Lean statement must conclude the supplied "
            "root proposition (possibly under explicit premises), and its "
            "`dependencies` must name only its immediate premises; transitive "
            "prerequisites belong on those premise claims. Give all other claims "
            "role `helper`. A role label is "
            "metadata only: the controller independently checks root "
            "equivalence and rejects unsupported premises."
            + (
                " EXCEPTION when the supplied root proposition mentions a "
                "`*_solution` placeholder: every claim statement mentioning a "
                "`*_solution` name is rejected, so root_assembly must NOT "
                "restate the placeholder. Determine the concrete answer from "
                "your own mathematical analysis and state root_assembly as "
                "the root proposition with your determined concrete value "
                "substituted for the placeholder (for example `... ↔ a = 2`), "
                "listing the claims that force that value in `dependencies`, "
                "and prove that closed statement."
                if (
                    solution_placeholder_filter_active
                    if solution_placeholder_filter_active is not None
                    else suppress_solution_placeholders
                )
                else ""
            )
        ),
        (
            "The dependencies must be an assembly contract, not just a story. "
            "If a downstream/root-reduction claim needs an extra premise that "
            "is not already a root hypothesis and is not exactly supplied by "
            "an earlier claim's conclusion, emit that extra premise as its "
            "own Lean-checkable claim first. Do not write handwave phrases "
            "like `then ensure the chosen witness lies in S`, `typically by "
            "showing S contains all positives`, or `once S contains the "
            "needed object` unless a prior dependency proves that precise "
            "fact."
        ),
        (
            "Keep branch-local reasoning explicit in Lean. If the math plan "
            "splits into cases, do not ask for a global theorem that silently "
            "assumes a branch. State each branch helper as a conditional "
            "Lean proposition whose branch hypothesis is a premise, for "
            "example `P -> target` and `Q -> target`, and list the case-split "
            "claim proving `P ∨ Q` in dependencies."
        ),
        (
            "Use only the supplied problem statement, root theorem, Lean "
            "signature, and verified helper summaries as evidence. If a claim "
            "needs a mathematical fact not already present there, state that "
            "fact as its own Lean-checkable obligation with truthful "
            "dependencies."
        ),
        (
            "`*_solution` names are answer placeholders, not reusable "
            "mathematical objects. Do not emit claims about their value, "
            "case split, equality to True/False, or expansion; decompose the "
            "active mathematical side of the root theorem instead."
            if suppress_solution_placeholders
            else ""
        ),
        (
            "For every numeric, cardinality, extremal, or counting formula "
            "claim, the JSON item must include a `sanity_check` explaining at "
            "least one tiny instance, boundary value, or complement check. If "
            "the check supports the exact emitted statement, set "
            "`sanity_status` to `passes`; if it fails, set it to `fails` and "
            "DO NOT emit that claim. For claims needing no check, use an empty "
            "`sanity_check` and `sanity_status: not_applicable`. "
            "The status is a required machine field, not prose. If "
            "the formula is derived by cases, include `counting_classification` "
            "listing the included cases. Do not strengthen, weaken, reverse, "
            "or otherwise change a quantified/comparative invariant unless "
            "the rationale explicitly proves that change. Sanity checks must "
            "show independent evidence; do not write `matches the listed "
            "check` unless the problem statement actually supplied a listed "
            "check. For a quantified implication with an equality conclusion, "
            "choose distinct values that make the equality conclusion false, "
            "then attempt to satisfy every premise, including existential and "
            "universal extremal premises. Equal-input or antecedent-false "
            "examples do not count as a sanity check."
        ),
        (
            "If a small-instance sanity check contradicts the proposed formula, "
            "do not emit the formula as a claim. Emit the structural "
            "classification lemma first, so the prover can repair the count "
            "from the exact predicate. The controller rejects any claim whose "
            "`sanity_check` says the claim is false, mismatched, refuted, or "
            "needs corrected coefficients; do not put known-bad formulas into "
            "JSON just to mark them for later repair."
        ),
        (
            "The same rule applies to every claim-local metadata field: never "
            "submit a claim while its `rationale` or `sanity_check` says that "
            "this claim is false as stated, must be corrected/replaced, or is "
            "being withdrawn. Emit only the corrected target. The controller "
            "withholds an explicitly withdrawn work item and every dependent "
            "claim before paid proof execution."
        ),
        (
            "Make the Lean statements type-correct — an ill-typed claim has no "
            "goal to prove and is dropped, which can taint the whole plan. Never "
            "pass implicit or instance arguments explicitly: write "
            "`Function.Injective f`, NOT `Injective (Fin 5) Int f`; when unsure, "
            "use the fully qualified declaration name with only its explicit "
            "arguments. Avoid "
            "ambiguous overloaded arithmetic: when an expression is integer-valued "
            "but an index has type Fin n, cast explicitly, for example "
            "((i : ℕ) : ℤ) or (i.1 : ℤ), before subtraction, powers, sums, or ring "
            "reasoning. NEVER apply subtraction, negation, absolute value (|·|), or "
            "fractional/possibly-negative division at type ℕ — ℕ has no negation "
            "so |·| and a - b silently truncate and comparisons like s / n < 0.8 "
            "are ℕ-division, not real; state such claims over ℤ or ℝ and cast the "
            "ℕ/Fin inputs first. Reference ONLY declarations that actually exist "
            "in Mathlib; do NOT invent identifiers — if you need a new notion, "
            "introduce it as its own def/abbrev claim that later claims depend on."
        ),
        (
            "Keep the decomposition faithful to the formal domain of the root "
            "statement. For elementary Nat/Int/Finset identities, prefer "
            "induction, reindexing, recurrence, finite case splits, and "
            "arithmetic normalization in those same types. Do not introduce "
            "Polynomial, PowerSeries, coefficient extraction, topology, measure, "
            "or other heavy new structures unless those objects already occur "
            "in the root statement/preamble or the plan includes type-correct "
            "bridge claims all the way back to the root language."
        ),
        (
            "For infinite sums/tsum problems, do not bundle final answer "
            "evaluation with unresolved Tonelli/Fubini, reindexing, index-shift, "
            "telescoping, or closed-form computation. Emit those as separate "
            "Lean-checkable bridge claims first; the controller rejects broad "
            "final-answer analytic claims that still hide those obligations."
        ),
        "",
        "Evidence rules:",
        "- Do not cite unavailable benchmark facts or problem-specific solved theorems.",
        "- Do not assume values or properties for constants that are not defined in the visible Lean context.",
        "- If the root contains a named target constant, plan the mathematical bridge needed to prove the visible proposition rather than treating the name itself as evidence.",
        "- Return planning JSON only; no Lean proof code and no prose wrapper.",
        "- Each `statement` must be a BARE Lean proposition/type only: NO "
        "`theorem`/`lemma` keyword, NO declaration name, NO `:= by`/proof body. "
        "WRONG: `theorem foo : P := by`. RIGHT: `P`.",
        "- The entire message must be one raw JSON object starting with `{` and "
        "ending with `}`. Do NOT wrap it in a ```json code fence, do NOT put it "
        "under a key such as `json`, and do NOT emit it as a quoted JSON string; "
        "emit the object itself.",
        "",
        "Root statement:",
        str(root_statement or "").strip(),
    ]
    if goal_block:
        parts.extend(["", "Current Lean goal state:", goal_block])
    if preamble_block:
        parts.extend(["", "Verified Lean context summary:", preamble_block])
    parts.extend(
        [
            "",
            "Return JSON with this shape:",
            json.dumps(
                {
                    "strategy": "proof decomposition summary naming the main bottleneck",
                    "plan_complete": False,
                    "claims": [
                        {
                            "name": "local_helper_name",
                            "role": "helper or root_assembly",
                            "statement": "Lean proposition to prove",
                            "rationale": "how this claim materially advances the root proof",
                            "invariant_refs": ["locked invariant names or phrases used"],
                            "sanity_check": "required for numeric/counting claims; otherwise empty",
                            "sanity_status": "passes, fails, or not_applicable",
                            "counting_classification": "required when a count is by cases; otherwise empty",
                            "dependencies": [
                                "exact earlier claim names supplying premises"
                            ],
                        }
                    ],
                    "notes": ["optional planner notes"],
                },
                indent=2,
            ),
            "",
            f"Keep the plan to at most {max(1, int(max_claims))} helper claims "
            "plus one root_assembly claim.",
            "Set `plan_complete` to true only when this response contains a "
            "root_assembly with a complete dependency chain to the root. Set "
            "it to false when another durable tranche is needed, even if this "
            "tranche includes a provisional root_assembly.",
        ]
    )
    return "\n".join(parts).strip()


def render_mini_subgoal_plan_summary(
    plan: MiniSubgoalPlan,
    *,
    include_variants: bool = True,
    max_variants_per_claim: int = 2,
) -> str:
    """Render a compact human-readable summary of a compiled plan."""

    lines: list[str] = []
    if plan.strategy:
        lines.append(f"Strategy: {plan.strategy}")
    if plan.plan_complete is not None:
        lines.append(f"Plan complete: {str(plan.plan_complete).lower()}")
    lines.append(f"Claims: {len(plan.claims)}")
    for idx, claim in enumerate(plan.claims, start=1):
        deps = f" deps=[{', '.join(claim.dependencies)}]" if claim.dependencies else ""
        role = f" role={claim.role}" if claim.role else ""
        lines.append(f"{idx}. {claim.name}{role}{deps}: {claim.statement}")
        if claim.rationale:
            lines.append(f"   why: {claim.rationale}")
        if claim.invariant_refs:
            lines.append(f"   invariants: {', '.join(claim.invariant_refs)}")
        if claim.sanity_check:
            lines.append(f"   sanity: {claim.sanity_check}")
        if claim.sanity_status:
            lines.append(f"   sanity_status: {claim.sanity_status}")
        if claim.counting_classification:
            lines.append(f"   cases: {claim.counting_classification}")
        if include_variants:
            for variant in claim.variants[: max(0, int(max_variants_per_claim))]:
                lines.append(f"   variant/{variant.mode}: {variant.statement}")
    if plan.notes:
        lines.append("Notes: " + "; ".join(plan.notes))
    return "\n".join(lines).strip()


def planner_visible_json_was_truncated(content: str) -> bool:
    """True when visible text opened a JSON value that never closed.

    A lying ``finish_reason=stop`` on a chopped prefix must not look complete
    just because claim-list salvage can reconstruct a helper-only fragment.
    Prose with no JSON opener is not truncation; parse-repair handles that.
    """

    text = str(content or "")
    start = _first_json_value_start(text)
    if start is None:
        return False
    opener = text[start]
    closer = "}" if opener == "{" else "]"
    return _balanced_json_end(text, start, opener, closer) is None


def _first_json_value_start(text: str) -> Optional[int]:
    in_string = False
    escaped = False
    for idx, ch in enumerate(text):
        if in_string:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            continue
        if ch == '"':
            in_string = True
            continue
        if ch in "{[":
            return idx
    return None


def _balanced_json_end(
    text: str,
    start: int,
    opener: str,
    closer: str,
) -> Optional[int]:
    depth = 0
    in_string = False
    escaped = False
    for idx in range(start, len(text)):
        ch = text[idx]
        if in_string:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            continue
        if ch == '"':
            in_string = True
        elif ch == opener:
            depth += 1
        elif ch == closer:
            depth -= 1
            if depth == 0:
                return idx
    return None


def _strip_jsonish_comments(text: str) -> str:
    """Remove ``//`` line and ``/* */`` block comments outside JSON strings.

    Reasoning models frequently annotate the JSON they emit with comments, which
    ``json.loads`` rejects.  String-aware so a ``//`` or ``/*`` *inside* a Lean
    statement string (e.g. integer division) is preserved verbatim.
    """

    out: list[str] = []
    i = 0
    n = len(text)
    in_string = False
    escaped = False
    while i < n:
        ch = text[i]
        if in_string:
            out.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if ch == '"':
            in_string = True
            out.append(ch)
            i += 1
            continue
        if ch == "/" and i + 1 < n and text[i + 1] == "/":
            nl = text.find("\n", i)
            if nl == -1:
                break
            i = nl
            continue
        if ch == "/" and i + 1 < n and text[i + 1] == "*":
            close = text.find("*/", i + 2)
            if close == -1:
                break
            i = close + 2
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def _strip_trailing_commas(text: str) -> str:
    """Drop commas that immediately precede ``}``/``]`` outside JSON strings.

    String-aware so a comma inside a Lean statement string (set-builder, tuples)
    is never touched.
    """

    out: list[str] = []
    n = len(text)
    in_string = False
    escaped = False
    for i, ch in enumerate(text):
        if in_string:
            out.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            continue
        if ch == '"':
            in_string = True
            out.append(ch)
            continue
        if ch == ",":
            j = i + 1
            while j < n and text[j] in " \t\r\n":
                j += 1
            if j < n and text[j] in "}]":
                # Skip this comma; the closer will be emitted normally.
                continue
        out.append(ch)
    return "".join(out)


def _leading_claim_object_array(raw: str) -> Optional[str]:
    """Return a leading top-level claim-object array followed by prose, if any."""

    text = str(raw or "")
    lead = len(text) - len(text.lstrip())
    if text[lead : lead + 1] != "[":
        return None
    end = _balanced_json_end(text, lead, "[", "]")
    if end is None:
        return None
    candidate = text[lead : end + 1]
    try:
        data = json.loads(candidate, strict=False)
    except Exception:
        return None
    if not isinstance(data, list):
        return None
    for item in data:
        if not isinstance(item, Mapping):
            continue
        if any(str(item.get(key) or "").strip() for key in _STATEMENT_KEYS):
            return candidate
    return None


def _skip_json_string(text: str, i: int) -> int:
    """Given ``text[i] == '"'``, return the index just past the closing quote.

    Returns ``-1`` when the string is TRUNCATED (runs to EOF without an
    unescaped closing quote). This is the unambiguous "closed vs truncated"
    signal callers need: a complete string whose closing quote is the very last
    character returns ``len(text)`` (a valid index), NOT ``-1`` — so callers must
    test ``>= 0`` for completeness, never ``< len`` (which would misclassify a
    complete-at-EOF string) nor ``raw[j-1] == '"'`` (which a truncation right
    after an escaped quote ``\\"`` would fool).
    """

    n = len(text)
    i += 1
    while i < n:
        ch = text[i]
        if ch == "\\":
            i += 2
            continue
        if ch == '"':
            return i + 1
        i += 1
    return -1


def _looks_like_json_object_start(raw: str, open_idx: int) -> bool:
    """Return True when ``raw[open_idx:]`` plausibly starts a JSON object."""

    j = open_idx + 1
    n = len(raw)
    while j < n and raw[j] in " \t\r\n":
        j += 1
    return j >= n or raw[j] in '"}'


def _claim_array_has_jsonish_object_continuation(raw: str, close_idx: int) -> bool:
    """True if a completed claim-list array is followed like an object value."""

    j = close_idx + 1
    n = len(raw)
    while j < n and raw[j] in " \t\r\n":
        j += 1
    # EOF means a likely truncated object missing only its final brace; ``}`` is
    # complete. A comma is valid only when it is followed by another quoted key,
    # not by prose such as "Actual plan:".
    if j >= n or raw[j] == "}":
        return True
    if raw[j] != ",":
        return False
    j += 1
    while j < n and raw[j] in " \t\r\n":
        j += 1
    return j < n and raw[j] == '"'


def _claim_path_has_non_plan_container(path: Sequence[str]) -> bool:
    return any(str(part or "").strip().lower() in _NON_PLAN_CONTAINER_KEYS for part in path)


def _claim_array_openers(raw: str) -> list[tuple[str, int, int, int, tuple[str, ...]]]:
    """Claim-list array openers with key, array index, depth, object start, path.

    A claim-list word is recognized only as a genuine JSON KEY: a quoted
    ``_CLAIM_LIST_KEYS`` token whose next non-whitespace char is ``:`` followed
    (after whitespace) by ``[``. This ignores claim-list words that appear as
    string *values* or array *elements* (e.g. ``"meta":["steps", ...]``). A
    leading top-level ``[`` (the whole response is itself an array) is reported
    with an empty key and depth 0. ``brace_depth`` is the number of currently
    open ``{`` enclosing the key (root keys = 1); the recovery caller uses it to
    prefer the SHALLOWEST ``claims`` array (so a nested ``claims`` cannot be
    recovered over the real top-level plan). String-aware; capped at
    ``_MAX_CLAIM_ARRAY_OPENERS`` to bound work on adversarial input.

    Note: depth is used for RELATIVE preference (shallowest wins), not an
    absolute filter. An absolute ``depth == 1`` filter was tried and rejected:
    stray unbalanced ``{`` openers inflate depth and would hide a legitimate
    plan buried after junk (which is the single shallowest opener and so still
    wins under relative preference).
    """

    openers: list[tuple[str, int, int, int, tuple[str, ...]]] = []
    lead = len(raw) - len(raw.lstrip())
    if raw[lead : lead + 1] == "[":
        openers.append(("", lead, 0, -1, ()))
    n = len(raw)
    i = 0
    object_stack: list[int] = []  # positions of currently-open '{' (string-aware)
    key_stack: list[str] = []  # parent object keys that introduced each object
    pending_object_key = ""
    while i < n:
        ch = raw[i]
        if ch == '"':
            j = _skip_json_string(raw, i)
            if j < 0:
                # Unterminated (truncated) string: the rest of the input is
                # inside it, so no further keys can be found — stop scanning.
                break
            word = raw[i + 1 : max(i + 1, j - 1)]
            i = j
            if word in _CLAIM_LIST_KEYS:
                k = i
                while k < n and raw[k] in " \t\r\n":
                    k += 1
                if k < n and raw[k] == ":":
                    k += 1
                    while k < n and raw[k] in " \t\r\n":
                        k += 1
                    if k < n and raw[k] == "[" and object_stack:
                        openers.append(
                            (
                                word,
                                k,
                                len(object_stack),
                                object_stack[-1],
                                tuple(key_stack),
                            )
                        )
                        if len(openers) >= _MAX_CLAIM_ARRAY_OPENERS:
                            break
                    if k < n and raw[k] == "{":
                        pending_object_key = word
                    else:
                        pending_object_key = ""
            else:
                k = i
                while k < n and raw[k] in " \t\r\n":
                    k += 1
                if k < n and raw[k] == ":":
                    pending_object_key = word
            continue
        if ch == "{":
            if _looks_like_json_object_start(raw, i):
                object_stack.append(i)
                key_stack.append(pending_object_key)
                pending_object_key = ""
        elif ch == "}":
            if object_stack:
                object_stack.pop()
                if key_stack:
                    key_stack.pop()
                pending_object_key = ""
        elif ch not in " \t\r\n:":
            pending_object_key = ""
        i += 1
    return openers


def _gather_complete_elements(raw: str, open_idx: int) -> list[str]:
    """Collect complete balanced ``{...}`` OBJECT elements inside the array at
    ``open_idx``.

    A ``"..."`` element is SKIPPED string-aware (so quoted braces never confuse
    object boundaries), NOT collected. Truncated STRING-element claim arrays are
    intentionally not salvaged here: that path repeatedly produced subtle
    regressions — a truncation landing on an escaped quote ``\\"``, a complete
    string ending exactly at EOF, and salvage re-emitting a string carrying an
    illegal JSON escape (a lone Lean/LaTeX backslash) — each yielding invalid
    salvage JSON. Such truncation now falls through to the planner repair-retry,
    which re-asks for a complete, valid plan. Stops at the closing ``]`` or the
    first truncated/incomplete element.
    """

    objects: list[str] = []
    i = open_idx + 1
    n = len(raw)
    while i < n:
        ch = raw[i]
        if ch == "]":
            break
        if ch == '"':
            j = _skip_json_string(raw, i)
            if j < 0:
                break  # truncated string element — stop
            i = j
            continue
        if ch != "{":
            i += 1
            continue
        end = _balanced_json_end(raw, i, "{", "}")
        if end is None:
            break
        objects.append(raw[i : end + 1])
        i = end + 1
    return objects


def _claims_key_rank(key: str) -> int:
    """Prefer the canonical ``claims`` key over outline-ish claim-list keys."""

    return 0 if key == "claims" else 1


def _salvage_truncated_claim_objects(text: str) -> Optional[str]:
    """Rebuild a clean ``{"claims": [obj, ...]}`` object from a TRUNCATED response.

    Locates every claim-list array opener (string-aware, key-validated), then
    salvages the first UNBALANCED (max-tokens-cut) one — preferring the canonical
    ``claims`` key, then source order — by collecting its complete leading
    ``{...}`` objects. Crucially, a preceding COMPLETE array (an outline key such
    as ``steps``/``subgoals``, or a schema-example ``claims`` array) no longer
    blinds salvage to the real truncated plan: balanced openers are skipped, not
    treated as "nothing to salvage". The result is wrapped as a keyed
    ``{"claims": [...]}`` object (not a bare array) so the salvaged real plan
    ranks as keyed and is not outranked by a complete keyed example. Returns
    ``None`` when there is no truncated claim array.
    """

    raw = str(text or "")
    openers = _claim_array_openers(raw)
    if not openers:
        return None
    for _key, idx, _depth, _obj_start, path in sorted(
        openers, key=lambda ko: (_claims_key_rank(ko[0]), ko[1])
    ):
        if _claim_path_has_non_plan_container(path):
            continue
        if _balanced_json_end(raw, idx, "[", "]") is not None:
            continue  # complete array — nothing to salvage here; try the next
        elements = _gather_complete_elements(raw, idx)
        if elements:
            # Wrap as a canonical claims object (not a bare array) so the
            # salvaged REAL plan is keyed — otherwise a complete keyed example
            # (e.g. a schema-restatement) would outrank it during selection.
            return '{"claims": [' + ",".join(elements) + "]}"
    return None


def _plan_parts_from_json(
    data: object,
) -> tuple[list[object], str, list[str], str]:
    if isinstance(data, list):
        return data, "", [], ""
    if not isinstance(data, Mapping):
        return [data], "", [], ""

    claims: object = None
    strategy = str(data.get("strategy") or data.get("summary") or "").strip()
    nested_notes: list[str] = []
    nested_root = ""
    for key in _CLAIM_LIST_KEYS:
        if key not in data:
            continue
        value = data.get(key)
        if key == "plan" and isinstance(value, str):
            strategy = strategy or value.strip()
            continue
        if key == "plan" and isinstance(value, Mapping):
            nested_claims, nested_strategy, nested_notes, nested_root = (
                _plan_parts_from_json(value)
            )
            claims = nested_claims
            strategy = strategy or nested_strategy
            break
        else:
            claims = value
            break
    if claims is None and any(data.get(key) for key in _STATEMENT_KEYS):
        claims = [data]
    if claims is None:
        claims = []
    if isinstance(claims, Mapping):
        # A single claim OBJECT (has a statement-defining key with a string
        # value) is one claim; only a dict-OF-claims (name -> claim) expands via
        # its values.  ``list(claims.values())`` on a lone claim object would
        # fabricate one bogus claim per field.
        if any(
            isinstance(claims.get(key), str) and str(claims.get(key)).strip()
            for key in _STATEMENT_KEYS
        ):
            claims = [claims]
        else:
            claims = list(claims.values())
    elif not isinstance(claims, list):
        claims = [claims]

    notes_raw = data.get("notes", ())
    if isinstance(notes_raw, str):
        notes = [notes_raw]
    elif isinstance(notes_raw, Iterable) and not isinstance(notes_raw, (bytes, str)):
        notes = [str(n) for n in notes_raw if str(n).strip()]
    else:
        notes = []
    notes.extend(nested_notes)

    return (
        list(claims),
        strategy,
        notes,
        str(data.get("root_statement") or nested_root or "").strip(),
    )


def _plan_completion_from_json(data: object) -> Optional[bool]:
    """Read the typed completion contract without changing plan-parts API."""

    if not isinstance(data, Mapping):
        return None
    raw_plan_complete = data.get("plan_complete")
    if isinstance(raw_plan_complete, bool):
        return raw_plan_complete
    nested = data.get("plan")
    if isinstance(nested, Mapping):
        return _plan_completion_from_json(nested)
    return None


def _claim_items(raw_claims: object) -> list[object]:
    if isinstance(raw_claims, MiniSubgoalPlan):
        return list(raw_claims.claims)
    if isinstance(raw_claims, Mapping):
        claims, _strategy, _notes, _root = _plan_parts_from_json(raw_claims)
        return claims
    if isinstance(raw_claims, (str, MiniSubgoalClaim)):
        return [raw_claims]
    if isinstance(raw_claims, Iterable):
        return list(raw_claims)
    return [raw_claims]


def _coerce_sanity_contract_version(value: object, *, required: bool) -> int:
    try:
        parsed = int(value or 0)
    except (TypeError, ValueError):
        parsed = 0
    return max(parsed, int(bool(required)))


def _coerce_claim(
    item: object,
    *,
    source_index: int,
    name_prefix: str = "mini_subgoal",
    require_sanity_contract: bool = False,
) -> Optional[MiniSubgoalClaim]:
    if isinstance(item, MiniSubgoalClaim):
        statement = str(item.statement or "").strip()
        if not statement:
            return None
        return MiniSubgoalClaim(
            name=item.name or sanitize_theorem_name(name_prefix, index=source_index),
            statement=statement,
            role=str(item.role or "").strip().lower(),
            rationale=str(item.rationale or "").strip(),
            invariant_refs=tuple(
                str(ref).strip() for ref in item.invariant_refs if str(ref).strip()
            ),
            sanity_check=str(item.sanity_check or "").strip(),
            sanity_status=str(item.sanity_status or "").strip().lower(),
            sanity_contract_version=_coerce_sanity_contract_version(
                getattr(item, "sanity_contract_version", 0),
                required=require_sanity_contract,
            ),
            counting_classification=str(item.counting_classification or "").strip(),
            dependencies=tuple(str(d).strip() for d in item.dependencies if str(d).strip()),
            variants=tuple(item.variants),
            source_index=item.source_index or source_index,
            source_arbitration_provisional=bool(
                item.source_arbitration_provisional
            ),
        )
    if isinstance(item, str):
        statement = item.strip()
        if not statement:
            return None
        return MiniSubgoalClaim(
            name=sanitize_theorem_name(name_prefix, index=source_index),
            statement=statement,
            source_index=source_index,
            sanity_contract_version=int(bool(require_sanity_contract)),
        )
    if not isinstance(item, Mapping):
        return None

    statement = ""
    for key in _STATEMENT_KEYS:
        if item.get(key):
            statement = str(item.get(key)).strip()
            break
    if not statement:
        return None

    raw_deps = item.get("dependencies", item.get("deps", item.get("uses", ())))
    if isinstance(raw_deps, str):
        dependencies = tuple(part.strip() for part in raw_deps.split(",") if part.strip())
    elif isinstance(raw_deps, Iterable):
        dependencies = tuple(str(dep).strip() for dep in raw_deps if str(dep).strip())
    else:
        dependencies = ()

    raw_invariants = item.get(
        "invariant_refs",
        item.get("invariants", item.get("uses_invariants", ())),
    )
    if isinstance(raw_invariants, str):
        invariant_refs = tuple(
            part.strip() for part in raw_invariants.split(",") if part.strip()
        )
    elif isinstance(raw_invariants, Iterable):
        invariant_refs = tuple(
            str(ref).strip() for ref in raw_invariants if str(ref).strip()
        )
    else:
        invariant_refs = ()

    return MiniSubgoalClaim(
        name=str(item.get("name") or item.get("theorem_name") or "").strip()
        or sanitize_theorem_name(name_prefix, index=source_index),
        statement=statement,
        role=str(item.get("role") or item.get("kind") or "").strip().lower(),
        rationale=str(item.get("rationale") or item.get("why") or "").strip(),
        invariant_refs=invariant_refs,
        sanity_check=str(
            item.get("sanity_check") or item.get("small_instance_check") or ""
        ).strip(),
        sanity_status=str(
            item.get("sanity_status")
            or item.get("sanity_result")
            or item.get("small_instance_status")
            or ""
        ).strip().lower(),
        sanity_contract_version=_coerce_sanity_contract_version(
            item.get("sanity_contract_version"),
            required=require_sanity_contract,
        ),
        counting_classification=str(
            item.get("counting_classification")
            or item.get("case_classification")
            or ""
        ).strip(),
        dependencies=dependencies,
        source_index=source_index,
    )


def _unique_name(
    name: str,
    used_names: set[str],
    *,
    fallback_index: int,
    prefix: str,
) -> str:
    base = sanitize_theorem_name(name, prefix=prefix) or sanitize_theorem_name(
        prefix,
        index=fallback_index,
    )
    candidate = base
    suffix = 2
    while candidate in used_names:
        # Append the disambiguator via ``index`` so sanitize_theorem_name
        # truncates the BASE (not the suffix) to fit ``max_length``.  Embedding
        # the suffix in the name string instead lets a max-length base truncate
        # it right back off, leaving ``candidate == base`` and spinning forever.
        candidate = sanitize_theorem_name(base, prefix=prefix, index=suffix)
        suffix += 1
    used_names.add(candidate)
    return candidate


def _dependency_key(raw: object) -> str:
    text = str(raw or "").strip()
    if not text:
        return ""
    sanitized = sanitize_theorem_name(text, prefix="dep", index=None, max_length=0)
    collapsed = re.sub(r"[^A-Za-z0-9']+", "_", text).strip("_")
    return (sanitized or collapsed or text).lower()


def _dependency_alias_keys(*names: object) -> set[str]:
    keys: set[str] = set()
    for name in names:
        text = str(name or "").strip()
        if not text:
            continue
        keys.add(_dependency_key(text))
        keys.add(_dependency_key(text.replace("_", " ")))
    return {key for key in keys if key}


def _assert_answer_safe_preamble_summary(
    summary: str,
    *,
    suppress_solution_placeholders: bool = True,
) -> None:
    text = str(summary or "")
    if not text or not suppress_solution_placeholders:
        return
    if "_solution" in text or _MATERIALIZED_SOLUTION_RE.search(text):
        raise ValueError(
            "answer_safe_preamble_summary must not include *_solution names "
            "or materialized answer definitions"
        )


def _format_goal_state(goal_state: object) -> str:
    if goal_state is None:
        return ""
    hypotheses = getattr(goal_state, "hypotheses", None) or ()
    target = str(getattr(goal_state, "target", "") or "").strip()
    lines: list[str] = []
    hyp_lines = [str(h).strip() for h in hypotheses if str(h).strip()]
    if hyp_lines:
        lines.append("hypotheses:")
        lines.extend(f"- {h}" for h in hyp_lines)
    if target:
        lines.append("target:")
        lines.append(target)
    return "\n".join(lines).strip()
