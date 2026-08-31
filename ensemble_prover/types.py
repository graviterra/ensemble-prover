"""Dependency-light shared schemas for theorem search and verification.

The module centralizes enums and dataclasses used across provider, Lean,
retrieval, search, and proof-state boundaries while avoiding import cycles.
Leaf schemas precede the composite records that contain them.
"""

from __future__ import annotations

import enum
import hashlib
import re
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any, Dict, List, Mapping, Optional, Tuple

if TYPE_CHECKING:
    from .lean_parser import GoalStateFeatures, LeanParseResult

_INTERNAL_OBLIGATION_HANDLE_RE = re.compile(
    r"\b(?:"
    r"obl_[A-Za-z0-9_]+|"
    r"(?:critical|support)_validated(?:_[A-Za-z0-9]+)*|"
    r"slot_[A-Za-z0-9_]+"
    r")\b"
)


def is_internal_obligation_handle(name: str) -> bool:
    """True for scaffold/root-contract handles that are not Lean globals."""
    ident = str(name or "").strip().strip("`'\" ")
    return bool(ident and _INTERNAL_OBLIGATION_HANDLE_RE.fullmatch(ident))


def redact_internal_obligation_handles(text: str) -> str:
    """Hide runtime obligation handles from prompt/human-facing summaries."""
    cleaned = str(text or "")
    if not cleaned:
        return ""
    return _INTERNAL_OBLIGATION_HANDLE_RE.sub("<internal-obligation>", cleaned)


# ── Proof signals (replaces string-encoded control flow in output) ────


class ProofSignal(enum.Enum):
    """Typed control signals carried by ProofResult.

    Replaces ad-hoc ``output.startswith("REPLAN_REQUESTED:")`` /
    ``output.startswith("self_reference:")`` string checks with an enum
    that can be pattern-matched and exhaustively audited.
    """

    NONE = "none"
    REPLAN_REQUESTED = "replan_requested"
    SELF_REFERENCE = "self_reference"


_WORKSET_SUPPORT_KINDS = {"helper_claim", "bridge_lemma"}
_WORKSET_SLOT_KINDS = {"scaffold_slot", "open_root_hole"}
_WORKSET_SOLVED_STATUSES = {"lean_verified", "materialized"}


def _workset_enum_value(value: Any) -> str:
    raw = getattr(value, "value", value)
    return str(raw or "").strip()


def _workset_nodes(workset: Any) -> List[Any]:
    nodes_fn = getattr(workset, "nodes", None)
    if not callable(nodes_fn):
        return []
    try:
        return list(nodes_fn() or [])
    except Exception:
        return []


def _workset_root_statement(workset: Any, nodes: List[Any]) -> str:
    root_name = str(getattr(workset, "root_claim_name", "") or "").strip()
    for node in nodes:
        name = str(getattr(node, "name", "") or "").strip()
        kind = _workset_enum_value(getattr(node, "kind", ""))
        if (root_name and name == root_name) or kind == "root_claim":
            statement = str(getattr(node, "statement", "") or "").strip()
            if statement:
                return statement
    return ""


def _workset_metadata(node: Any) -> Dict[str, Any]:
    metadata = getattr(node, "metadata", None)
    return dict(metadata) if isinstance(metadata, Mapping) else {}


def _workset_node_statement(node: Any) -> str:
    metadata = _workset_metadata(node)
    for key in (
        "claim_statement",
        "execution_statement",
        "goal_target",
        "source_claim_statement",
    ):
        value = str(metadata.get(key, "") or "").strip()
        if value:
            return value
    return str(getattr(node, "statement", "") or "").strip()


def _workset_support_names(workset: Any, nodes: List[Any]) -> List[str]:
    node_support_names = sorted(
        str(getattr(node, "name", "") or "").strip()
        for node in nodes
        if _workset_enum_value(getattr(node, "kind", "")) in _WORKSET_SUPPORT_KINDS
        and _workset_enum_value(getattr(node, "status", "")) in _WORKSET_SOLVED_STATUSES
        and str(getattr(node, "name", "") or "").strip()
    )
    node_support_set = set(node_support_names)
    support_fn = getattr(workset, "support_for_root", None)
    if callable(support_fn):
        try:
            reported = [
                str(name or "").strip()
                for name in list(support_fn() or [])
                if str(name or "").strip()
            ]
            if nodes:
                return [name for name in reported if name in node_support_set]
            return reported
        except Exception:
            pass
    return node_support_names


def _workset_support_nodes(workset: Any, nodes: List[Any]) -> List[Any]:
    support_names = set(_workset_support_names(workset, nodes))
    return [
        node
        for node in nodes
        if str(getattr(node, "name", "") or "").strip() in support_names
    ]


def _workset_fingerprint(*parts: Any) -> str:
    payload = repr(parts).encode("utf-8", errors="replace")
    return hashlib.sha1(payload).hexdigest()[:16]


def _workset_int(value: Any, default: int = 0) -> int:
    try:
        return int(value)
    except Exception:
        return default


def _workset_str_list(value: Any) -> List[str]:
    if isinstance(value, str):
        return [value] if value else []
    if isinstance(value, (list, tuple, set)):
        return [str(item or "").strip() for item in value if str(item or "").strip()]
    return []


# ── Leaf types (no cross-module dataclass dependencies) ───────────────


@dataclass
class ProofResult:
    ok: bool
    proof: Optional[str]
    output: str
    signal: ProofSignal = ProofSignal.NONE
    signal_payload: str = ""
    file_path: Optional[str] = None
    parsed: Optional[Any] = (
        None  # LeanParseResult, carried per-result for parallel safety
    )
    returncode: Optional[int] = None
    validated_complete: bool = False
    lean_invocations: int = 0
    cache_hits: int = 0


@dataclass
class CandidateFailure:
    proof: str
    output: str
    parsed: Optional[LeanParseResult] = None
    progress: float = 0.0
    prompt_state: Optional[Any] = (
        None  # candidate-local prompt snapshot for later feedback
    )


@dataclass
class FailureRoundSummary:
    """Compact digest of one prove_statement round's failures."""

    round_idx: int
    candidate_count: int
    error_counts: Dict[str, int]  # error_type -> count
    strategy_counts: Dict[str, int]  # tactic tag -> count
    representative_errors: List[str]  # Top N actual Lean error messages (truncated)
    best_progress: float = 0.0  # Highest progress score in this round
    scope_key: str = ""  # Statement/support scope for chronology grouping
    event_idx: int = 0  # Monotonic creation order across scopes
    remaining_goal_count: int = 0  # Max unsolved_goal_count seen in this round
    remaining_goal_targets: List[str] = field(
        default_factory=list
    )  # Deduplicated goal targets
    type_mismatch_examples: List[Tuple[str, str]] = field(
        default_factory=list
    )  # (expected, actual) pairs
    # Partial-proof capture for cross-round progress carry-over. When a
    # composition/refinement round produces a candidate that made real
    # structural progress (intros/have/apply before failing), its proof
    # prefix is stashed here so the next round can extend it instead of
    # restarting from the root goal. Empty when no candidate in the round
    # exceeded the progress/shape threshold (see
    # Orchestrator._aggregate_failure_round).
    best_progress_proof: str = ""


@dataclass
class RefinerPattern:
    """Structural recipe extracted from a refiner success for prover re-use.

    Captures the bridge insight — which Mathlib lemma or structural move
    the refiner used to fix the prover's failing proof — so the prover
    can apply the same pattern on similar future goals.
    """

    goal_head: str = ""  # Outermost type constructor, e.g. "IntervalIntegrable"
    goal_domain: str = ""  # Problem domain, e.g. "analysis", "number_theory"
    original_error_type: str = ""  # The prover's error that the refiner fixed
    bridge_lemma: str = ""  # Key Mathlib lemma, e.g. "ContinuousOn.intervalIntegrable"
    bridge_claim: str = ""  # The `have`/`suffices` statement (truncated)
    tactic_skeleton: Tuple[str, ...] = ()  # Ordered tactic sequence
    statement_hash: str = ""  # Hash of the goal statement for dedup
    timestamp: float = 0.0
    use_count: int = 0  # Times surfaced to prover
    hit_count: int = 0  # Times prover succeeded after seeing it

    def to_dict(self) -> Dict[str, Any]:
        return {
            "goal_head": self.goal_head,
            "goal_domain": self.goal_domain,
            "original_error_type": self.original_error_type,
            "bridge_lemma": self.bridge_lemma,
            "bridge_claim": self.bridge_claim,
            "tactic_skeleton": list(self.tactic_skeleton),
            "statement_hash": self.statement_hash,
            "timestamp": self.timestamp,
            "use_count": self.use_count,
            "hit_count": self.hit_count,
        }

    @staticmethod
    def from_dict(data: Dict[str, Any]) -> "RefinerPattern":
        return RefinerPattern(
            goal_head=str(data.get("goal_head", "") or ""),
            goal_domain=str(data.get("goal_domain", "") or ""),
            original_error_type=str(data.get("original_error_type", "") or ""),
            bridge_lemma=str(data.get("bridge_lemma", "") or ""),
            bridge_claim=str(data.get("bridge_claim", "") or ""),
            tactic_skeleton=(
                tuple(data.get("tactic_skeleton", ()) or ())
                if not isinstance(data.get("tactic_skeleton"), str)
                else (str(data["tactic_skeleton"]),)
            ),
            statement_hash=str(data.get("statement_hash", "") or ""),
            timestamp=float(data.get("timestamp", 0.0) or 0.0),
            use_count=int(data.get("use_count", 0) or 0),
            hit_count=int(data.get("hit_count", 0) or 0),
        )

    def render_for_prompt(self) -> str:
        """Render as a natural-language recipe for the prover prompt."""
        preamble_parts: List[str] = []
        if self.goal_head:
            preamble_parts.append(f"For `{self.goal_head}` goals")
        if self.original_error_type:
            preamble_parts.append(f"(common error: {self.original_error_type})")
        body_parts: List[str] = []
        if self.bridge_lemma:
            body_parts.append(f"use `{self.bridge_lemma}` as the key bridge")
        if self.bridge_claim:
            body_parts.append(f"by establishing `{self.bridge_claim[:120]}`")
        if self.tactic_skeleton:
            body_parts.append(f"then: {' -> '.join(self.tactic_skeleton[:8])}")
        if preamble_parts and body_parts:
            return " ".join(preamble_parts) + ": " + " ".join(body_parts)
        if preamble_parts:
            return " ".join(preamble_parts)
        return " ".join(body_parts) if body_parts else ""


@dataclass
class SubgoalOutcome:
    """Outcome of a single subgoal from a previous planning round."""

    statement: str
    solved: bool
    error_type: (
        str  # "type_mismatch" | "timeout" | "exhausted" | "replan_requested" etc.
    )
    attempts: int
    score: float  # best score achieved (0.0–1.0)
    error_summary: str = ""  # first line of Lean error (truncated)


@dataclass
class DirectedHint:
    """A machine-actionable hint from the refiner/planner."""

    lemma: str  # "lemma_10332ea3"
    term: Optional[str] = None  # "(lemma_10332ea3 _).2" if known
    projection: Optional[int] = None  # 1 or 2 for And-projection
    strength: int = 100
    source: str = "refiner"  # "refiner" | "planner" | "projection"
    reason: str = ""


@dataclass(frozen=True)
class ExecutableObligation:
    """One live proof obligation exposed to prompt and execution lanes."""

    obligation_id: str
    statement: str
    original_statement: str = ""
    source: str = ""
    sources: List[str] = field(default_factory=list)
    roles: List[str] = field(default_factory=list)
    binding_state: str = "binding"
    admission_mode: str = ""
    validated: bool = False
    solved: bool = False
    dependency_ids: List[str] = field(default_factory=list)
    dependency_statements: List[str] = field(default_factory=list)
    score: float = 0.0
    error_type: str = ""
    error_summary: str = ""


@dataclass(frozen=True)
class ObligationPromptBundle:
    """Structured proof-intent bundle for prover/refiner/composition prompts."""

    active: Optional[ExecutableObligation] = None
    prerequisites: List[ExecutableObligation] = field(default_factory=list)
    bridge_support: List[ExecutableObligation] = field(default_factory=list)
    reformulations: List[ExecutableObligation] = field(default_factory=list)
    root_statement: str = ""
    focus_note: str = ""

    @property
    def has_content(self) -> bool:
        return bool(
            self.active
            or self.prerequisites
            or self.bridge_support
            or self.reformulations
            or str(self.focus_note or "").strip()
        )


@dataclass
class ProofCheckStats:
    """Per-invocation proof-check accounting for one prove_statement call."""

    total_checks: int = 0
    candidate_verification_checks: int = 0
    direct_checks: int = 0
    auxiliary_checks: int = 0
    lean_invocations: int = 0
    lean_prechecks: int = 0
    lean_oracle_checks: int = 0
    lean_total_invocations: int = 0
    cache_hits: int = 0


@dataclass
class CandidateSourceRef:
    """Typed ancestry edge for provenance outside the Layer 3 cluster path."""

    tag: str = ""
    origin: str = ""
    channel: str = ""
    transform_family: str = ""
    strategy_family: str = ""
    source_theorem: str = ""
    used_lemmas: List[str] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "tag": str(self.tag),
            "origin": str(self.origin),
            "channel": str(self.channel),
            "transform_family": str(self.transform_family),
            "strategy_family": str(self.strategy_family),
            "source_theorem": str(self.source_theorem),
            "used_lemmas": list(self.used_lemmas),
        }

    @classmethod
    def from_dict(cls, data: Any) -> "CandidateSourceRef":
        if isinstance(data, cls):
            return cls(
                tag=str(data.tag or ""),
                origin=str(data.origin or ""),
                channel=str(data.channel or ""),
                transform_family=str(data.transform_family or ""),
                strategy_family=str(data.strategy_family or ""),
                source_theorem=str(data.source_theorem or ""),
                used_lemmas=list(data.used_lemmas or []),
            )
        if any(
            hasattr(data, attr)
            for attr in ("tag", "origin", "channel", "transform_family")
        ):
            return cls(
                tag=str(getattr(data, "tag", "") or ""),
                origin=str(getattr(data, "origin", "") or ""),
                channel=str(getattr(data, "channel", "") or ""),
                transform_family=str(getattr(data, "transform_family", "") or ""),
                strategy_family=str(getattr(data, "strategy_family", "") or ""),
                source_theorem=str(getattr(data, "source_theorem", "") or ""),
                used_lemmas=list(getattr(data, "used_lemmas", []) or []),
            )
        if isinstance(data, dict):
            return cls(
                tag=str(data.get("tag", "") or ""),
                origin=str(data.get("origin", "") or ""),
                channel=str(data.get("channel", "") or ""),
                transform_family=str(data.get("transform_family", "") or ""),
                strategy_family=str(data.get("strategy_family", "") or ""),
                source_theorem=str(data.get("source_theorem", "") or ""),
                used_lemmas=list(data.get("used_lemmas", []) or []),
            )
        if isinstance(data, str):
            return cls(tag=str(data or ""))
        return cls()


@dataclass
class CandidateSource:
    """Provenance metadata for a scored proof candidate.

    ``tag`` is retained as a coarse compatibility projection for Layer 3 and
    legacy consumers. The primary provenance ontology is carried by the
    structured fields below:

    - ``channel`` records the acquisition channel (`generation`, `closure`,
      `feedback`, `heuristic`, ...).
    - ``transform_family`` records the structural transform (`identity`,
      `arithmetic_dual`, `semantic_memory`, ...).
    - ``strategy_family`` keeps the tactic taxonomy explicit but separate from
      the provenance taxonomy.
    - ``lineage_*`` preserves ancestry across closure transforms.
    - ``induced_by_*`` records the live candidate families that induced a
      semantic-memory recall.
    """

    tag: str = ""
    origin: str = ""
    channel: str = ""
    transform_family: str = ""
    strategy_family: str = ""
    lineage_sources: List[CandidateSourceRef] = field(default_factory=list)
    lineage_tags: List[str] = field(default_factory=list)
    lineage_origins: List[str] = field(default_factory=list)
    induced_by_sources: List[CandidateSourceRef] = field(default_factory=list)
    induced_by_tags: List[str] = field(default_factory=list)
    induced_by_origins: List[str] = field(default_factory=list)
    source_theorem: str = ""
    used_lemmas: List[str] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        """Return a JSON-safe structured provenance payload."""
        return {
            "tag": str(self.tag),
            "origin": str(self.origin),
            "channel": str(self.channel),
            "transform_family": str(self.transform_family),
            "strategy_family": str(self.strategy_family),
            "lineage_sources": [value.to_dict() for value in self.lineage_sources],
            "lineage_tags": list(self.lineage_tags),
            "lineage_origins": list(self.lineage_origins),
            "induced_by_sources": [
                value.to_dict() for value in self.induced_by_sources
            ],
            "induced_by_tags": list(self.induced_by_tags),
            "induced_by_origins": list(self.induced_by_origins),
            "source_theorem": str(self.source_theorem),
            "used_lemmas": list(self.used_lemmas),
        }

    @classmethod
    def from_dict(cls, data: Any) -> "CandidateSource":
        """Build a structured provenance record from dict/compat input."""
        if isinstance(data, cls):
            return cls(
                tag=str(data.tag or ""),
                origin=str(data.origin or ""),
                channel=str(data.channel or ""),
                transform_family=str(data.transform_family or ""),
                strategy_family=str(data.strategy_family or ""),
                lineage_sources=[
                    CandidateSourceRef.from_dict(v)
                    for v in (data.lineage_sources or [])
                ],
                lineage_tags=list(data.lineage_tags or []),
                lineage_origins=list(data.lineage_origins or []),
                induced_by_sources=[
                    CandidateSourceRef.from_dict(v)
                    for v in (data.induced_by_sources or [])
                ],
                induced_by_tags=list(data.induced_by_tags or []),
                induced_by_origins=list(data.induced_by_origins or []),
                source_theorem=str(data.source_theorem or ""),
                used_lemmas=list(data.used_lemmas or []),
            )
        if isinstance(data, dict):
            return cls(
                tag=str(data.get("tag", "") or ""),
                origin=str(data.get("origin", "") or ""),
                channel=str(data.get("channel", "") or ""),
                transform_family=str(data.get("transform_family", "") or ""),
                strategy_family=str(data.get("strategy_family", "") or ""),
                lineage_sources=[
                    CandidateSourceRef.from_dict(v)
                    for v in list(data.get("lineage_sources", []) or [])
                ],
                lineage_tags=list(data.get("lineage_tags", []) or []),
                lineage_origins=list(data.get("lineage_origins", []) or []),
                induced_by_sources=[
                    CandidateSourceRef.from_dict(v)
                    for v in list(data.get("induced_by_sources", []) or [])
                ],
                induced_by_tags=list(data.get("induced_by_tags", []) or []),
                induced_by_origins=list(data.get("induced_by_origins", []) or []),
                source_theorem=str(data.get("source_theorem", "") or ""),
                used_lemmas=list(data.get("used_lemmas", []) or []),
            )
        if isinstance(data, str):
            return cls(tag=str(data or ""))
        return cls()

    @classmethod
    def from_compat(
        cls,
        *,
        source: Any = None,
        tag: str = "",
        origin: str = "",
        channel: str = "",
        transform_family: str = "",
        strategy_family: str = "",
        lineage_sources: Optional[List[Any]] = None,
        lineage_tags: Optional[List[str]] = None,
        lineage_origins: Optional[List[str]] = None,
        induced_by_sources: Optional[List[Any]] = None,
        induced_by_tags: Optional[List[str]] = None,
        induced_by_origins: Optional[List[str]] = None,
        source_theorem: str = "",
        used_lemmas: Optional[List[str]] = None,
    ) -> "CandidateSource":
        """Merge structured provenance from *source* with flat kwargs as fallbacks.

        Fields already populated on the structured source take precedence;
        flat kwargs fill in any gaps.
        """
        if source is not None:
            structured = cls.from_dict(source)
        else:
            structured = cls()
        # Merge: structured fields win, kwargs fill gaps.
        return cls(
            tag=str(structured.tag or tag or ""),
            origin=str(structured.origin or origin or ""),
            channel=str(structured.channel or channel or ""),
            transform_family=str(structured.transform_family or transform_family or ""),
            strategy_family=str(structured.strategy_family or strategy_family or ""),
            lineage_sources=(
                structured.lineage_sources
                or [
                    CandidateSourceRef.from_dict(v) for v in list(lineage_sources or [])
                ]
            ),
            lineage_tags=list(structured.lineage_tags or lineage_tags or []),
            lineage_origins=list(structured.lineage_origins or lineage_origins or []),
            induced_by_sources=(
                structured.induced_by_sources
                or [
                    CandidateSourceRef.from_dict(v)
                    for v in list(induced_by_sources or [])
                ]
            ),
            induced_by_tags=list(structured.induced_by_tags or induced_by_tags or []),
            induced_by_origins=list(
                structured.induced_by_origins or induced_by_origins or []
            ),
            source_theorem=str(structured.source_theorem or source_theorem or ""),
            used_lemmas=list(structured.used_lemmas or used_lemmas or []),
        )


@dataclass
class CandidateInfo:
    text: str
    embedding: List[float]
    distance: float
    novelty: float
    utility: float
    cost: float
    goal_alignment: float
    quality: float
    overlap: float
    balance: float
    trivial: float
    bad: float
    score: float
    degenerate: float = 0.0
    compute_cost: float = 0.0
    prediction: float = 0.0
    strategy_alignment: float = 0.0
    strategy_family: str = ""
    source_model: Optional[str] = None
    strategy_override: Optional[str] = None
    source: CandidateSource = field(default_factory=CandidateSource)
    predicted_delta: List[float] = field(default_factory=list)
    admission_score: float = 0.0
    admission_mode: str = ""
    admission_reason: str = ""
    consistency_state: str = ""
    admitted: bool = True

    def __post_init__(self) -> None:
        if not isinstance(self.source, CandidateSource):
            self.source = CandidateSource.from_dict(self.source)
        # Sync strategy_family bidirectionally; source wins on disagreement
        # since it carries richer provenance context.
        if self.source.strategy_family:
            self.strategy_family = str(self.source.strategy_family)
        elif self.strategy_family:
            self.source.strategy_family = str(self.strategy_family)

    @property
    def source_tag(self) -> str:
        return str(self.source.tag or "")

    @source_tag.setter
    def source_tag(self, value: str) -> None:
        self.source.tag = str(value or "")

    @property
    def source_origin(self) -> str:
        return str(self.source.origin or "")

    @source_origin.setter
    def source_origin(self, value: str) -> None:
        self.source.origin = str(value or "")

    @property
    def source_channel(self) -> str:
        return str(self.source.channel or "")

    @source_channel.setter
    def source_channel(self, value: str) -> None:
        self.source.channel = str(value or "")

    @property
    def source_transform_family(self) -> str:
        return str(self.source.transform_family or "")

    @source_transform_family.setter
    def source_transform_family(self, value: str) -> None:
        self.source.transform_family = str(value or "")

    @property
    def source_lineage_tags(self) -> List[str]:
        return self.source.lineage_tags

    @source_lineage_tags.setter
    def source_lineage_tags(self, value: List[str]) -> None:
        self.source.lineage_tags = list(value or [])

    @property
    def source_lineage_sources(self) -> List[CandidateSourceRef]:
        return self.source.lineage_sources

    @source_lineage_sources.setter
    def source_lineage_sources(self, value: List[Any]) -> None:
        self.source.lineage_sources = [
            CandidateSourceRef.from_dict(v) for v in list(value or [])
        ]

    @property
    def source_lineage_origins(self) -> List[str]:
        return self.source.lineage_origins

    @source_lineage_origins.setter
    def source_lineage_origins(self, value: List[str]) -> None:
        self.source.lineage_origins = list(value or [])

    @property
    def source_induced_by_tags(self) -> List[str]:
        return self.source.induced_by_tags

    @source_induced_by_tags.setter
    def source_induced_by_tags(self, value: List[str]) -> None:
        self.source.induced_by_tags = list(value or [])

    @property
    def source_induced_by_sources(self) -> List[CandidateSourceRef]:
        return self.source.induced_by_sources

    @source_induced_by_sources.setter
    def source_induced_by_sources(self, value: List[Any]) -> None:
        self.source.induced_by_sources = [
            CandidateSourceRef.from_dict(v) for v in list(value or [])
        ]

    @property
    def source_induced_by_origins(self) -> List[str]:
        return self.source.induced_by_origins

    @source_induced_by_origins.setter
    def source_induced_by_origins(self, value: List[str]) -> None:
        self.source.induced_by_origins = list(value or [])

    @property
    def source_theorem(self) -> str:
        return str(self.source.source_theorem or "")

    @source_theorem.setter
    def source_theorem(self, value: str) -> None:
        self.source.source_theorem = str(value or "")

    @property
    def source_used_lemmas(self) -> List[str]:
        return self.source.used_lemmas

    @source_used_lemmas.setter
    def source_used_lemmas(self, value: List[str]) -> None:
        self.source.used_lemmas = list(value or [])


@dataclass(frozen=True)
class Layer3ClusterSignature:
    """Structured identity for a Layer 3 residual cluster."""

    channel: str
    transform_family: str
    tag: str

    def as_dict(self) -> Dict[str, str]:
        """Return a JSON-safe view used by telemetry and rupture events."""
        return {
            "channel": str(self.channel),
            "transform_family": str(self.transform_family),
            "tag": str(self.tag),
        }


@dataclass
class StrategyGoal:
    """A proposed strategy-level goal for the ensemble."""

    name: str
    priority: float
    recommended_tactics: List[str]
    rationale: str


class EnsembleMode(enum.Enum):
    """Explicit operational mode for the ensemble controller."""

    AUTO = "auto"
    FORMAL = "formal"
    LEARNED = "learned"


# Backward-compatible alias while keeping a single canonical enum.
AdmissionMode = EnsembleMode


@dataclass(frozen=True)
class MasterPolicy:
    """Runtime policy overrides produced by the Ensemble when acting as MEO.

    All fields are optional; when None, the base config value should be used.
    """

    strategy_mode: Optional[str] = None  # "linear" | "beam" | "mcts" | "tactic_tree"
    best_of_n: Optional[int] = None
    candidates_per_goal: Optional[int] = None
    refine_rounds: Optional[int] = None
    planner_subgoals_max: Optional[int] = None
    max_depth: Optional[int] = None
    tactic_tree_enabled: Optional[bool] = None
    retrieval_rerank_mode: Optional[str] = None  # "none" | "cross_encoder" | "llm"
    retrieval_rerank_top_n: Optional[int] = None
    prompt_budget_tokens: Optional[int] = None
    # LLM policy overrides.
    llm_temperature_scale: Optional[float] = None
    planner_use_json: Optional[bool] = None
    # Lean verification policy overrides.
    lean_timeout_s: Optional[float] = None
    lean_fast_fail_timeout_s: Optional[float] = None
    lean_precheck_mode: Optional[str] = None  # "none" | "typecheck" | "strict"
    lean_precheck_timeout_s: Optional[float] = None
    lean_max_full_checks: Optional[int] = None
    lean_min_score_full_check: Optional[float] = None
    # Explicit closure / admission policy surface for literal-V3 control.
    controller_mode: Optional[str] = None  # "auto" | "formal" | "learned"
    formal_consistency_mode: Optional[str] = None  # "syntactic" | "theorem_prover"
    negation_closure_enabled: Optional[bool] = None
    negation_closure_max_expansion: Optional[int] = None
    semantic_closure_enabled: Optional[bool] = None
    semantic_closure_max: Optional[int] = None
    admission_formal_threshold: Optional[float] = None
    admission_learned_threshold: Optional[float] = None
    learned_collapse_enabled: Optional[bool] = None
    learned_collapse_threshold: Optional[float] = None
    learned_collapse_similarity_threshold: Optional[float] = None
    # Adaptive search fields (set by MEO, respected by orchestrator/search callbacks).
    time_budget_s: Optional[float] = None
    formalization_reserve_s: Optional[float] = None
    stale_fraction: Optional[float] = None
    early_exit_min_iterations: Optional[int] = None
    early_exit_min_nodes: Optional[int] = None
    early_exit_boilerplate_threshold: Optional[float] = None
    # Recursive replanning control (set by MEO, respected by restart loop).
    replan_enabled: Optional[bool] = None  # None = use config default
    replan_strategy_hint: Optional[str] = (
        None  # "simpler" | "deeper" | "alternative" | None
    )
    note: str = ""


@dataclass
class ResourceLimits:
    """Resource constraints threaded through scoring and goal selection."""

    budget_time: float = 1800.0
    budget_attempts: int = 200
    elapsed_time: float = 0.0
    used_attempts: int = 0
    total_compute: float = 0.0

    @property
    def time_remaining_frac(self) -> float:
        if self.budget_time <= 0:
            return 0.0
        return max(0.0, min(1.0, 1.0 - self.elapsed_time / self.budget_time))

    @property
    def attempts_remaining_frac(self) -> float:
        if self.budget_attempts <= 0:
            return 0.0
        return max(0.0, min(1.0, 1.0 - self.used_attempts / self.budget_attempts))

    @property
    def budget_pressure(self) -> float:
        """0.0 = fresh budget, 1.0 = budget exhausted."""
        return 1.0 - min(self.time_remaining_frac, self.attempts_remaining_frac)


@dataclass(frozen=True)
class BudgetContext:
    """Immutable per-phase cost budget.

    Replaces the mutable ``_cost_ceiling_usd`` scalar that was shared across
    search and formalization phases.  Each phase constructs its own context;
    no shared mutable ceiling state.

    Fields:
        ceiling_usd:       Maximum USD spend allowed in this phase (0 = unlimited).
        phase:             Human-readable phase name for diagnostics.
        deadline_unix:     Wall-clock deadline (``time.time()`` value).
                           0 means no deadline.  Propagated into LLM retry loops
                           so retries cannot exceed the phase budget.
        started_at:        Wall-clock start of this phase (``time.time()`` value).
        exempt_baseline_s: Value of ``_budget_exempt_time_s`` when this phase
                           started.  Used by ``_llm_deadline()`` to slide the
                           deadline forward as exempt time (Lean checks,
                           retrieval) accumulates.
    """

    ceiling_usd: float = 0.0
    phase: str = "init"
    deadline_unix: float = 0.0
    started_at: float = 0.0
    exempt_baseline_s: float = 0.0

    def is_cost_exceeded(self, current_cost_usd: float) -> bool:
        """Return True if *current_cost_usd* meets or exceeds the ceiling."""
        if self.ceiling_usd <= 0:
            return False
        return current_cost_usd >= self.ceiling_usd


@dataclass
class ComplexityState:
    """Output of grow/prune: adjustments to search parameters."""

    complexity: float = 1.0
    action: str = "noop"
    action_dim: str = ""
    typed_action: str = ""
    controller_mode: str = ""
    policy: Optional[MasterPolicy] = None
    candidates_adj: int = 0
    refine_adj: int = 0
    # E4: dimension-informed adjustments from delta analysis
    temperature_adj: float = 0.0  # LLM temperature delta (clamped ±0.15)
    retrieval_boost: float = 0.0  # Retrieval min_score adjustment (clamped ±0.1)
    best_strategy: str = ""  # Recommended strategy tag from delta analysis
    action_dimension: str = ""  # Typed controller axis (e.g. search_width)


@dataclass
class EnsembleControlPolicy:
    """First-class mutable controller policy applied across proof cycles."""

    controller_mode: str = "auto"
    formal_consistency_mode: str = "theorem_prover"
    semantic_closure_enabled: bool = True
    semantic_closure_max: int = 5
    negation_closure_enabled: bool = True
    negation_closure_max: int = 3
    lean_precheck_mode: str = "typecheck"
    lean_max_full_checks: Optional[int] = None
    lean_min_score_full_check: Optional[float] = None
    admission_formal_threshold: float = 0.20
    admission_learned_threshold: float = 0.15
    learned_collapse_enabled: bool = True
    learned_collapse_threshold: float = 0.55
    learned_collapse_similarity_threshold: float = 0.90
    candidates_bias: int = 0
    refine_bias: int = 0
    temperature_adjust: float = 0.0
    retrieval_boost: float = 0.0
    best_strategy_hint: str = ""
    last_action: str = ""
    last_action_dim: str = ""
    last_typed_action: str = ""
    note: str = ""


@dataclass
class AdmissionRecord:
    """One admission-pipeline decision for a candidate or context artifact."""

    key: str
    kind: str
    value: str = ""
    accepted: bool = False
    stage: str = ""
    reason: str = ""
    score: float = 0.0
    error_type: str = ""
    metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass
class AdmittedState:
    """Canonical admitted-state snapshot (`sT`) for one goal/problem cycle.

    The orchestrator keeps legacy prompt/scope fields for compatibility, but
    admission decisions should be recorded here so candidates, proven lemmas,
    and context artifacts share a single lifecycle model.
    """

    statement: str = ""
    cycle: int = 0
    mode: str = EnsembleMode.AUTO.value
    considered_count: int = 0
    admitted_count: int = 0
    rejected_count: int = 0
    last_action: str = ""
    last_action_dim: str = ""
    stable_margin: float = 0.0
    tail_distance: float = 0.0
    dispersion: float = 0.0
    resource_pressure: float = 0.0
    consistency_stage: str = "syntactic"
    candidate_records: Dict[str, AdmissionRecord] = field(default_factory=dict)
    context_records: Dict[str, AdmissionRecord] = field(default_factory=dict)
    accepted_candidate_order: List[str] = field(default_factory=list)
    verification_candidate_order: List[str] = field(default_factory=list)
    accepted_context_names: List[str] = field(default_factory=list)
    rejected_context_names: List[str] = field(default_factory=list)
    policy_note: str = ""
    active_goal_name: str = ""
    delta_geometry: Optional["DeltaGeometryState"] = None
    control_policy: Optional["EnsembleControlPolicy"] = None

    def reset(
        self,
        *,
        statement: str = "",
        cycle: int = 0,
        mode: str = EnsembleMode.AUTO.value,
    ) -> None:
        self.statement = str(statement or "")
        self.cycle = int(cycle)
        self.mode = str(mode or EnsembleMode.AUTO.value)
        self.considered_count = 0
        self.admitted_count = 0
        self.rejected_count = 0
        self.last_action = ""
        self.last_action_dim = ""
        self.stable_margin = 0.0
        self.tail_distance = 0.0
        self.dispersion = 0.0
        self.resource_pressure = 0.0
        self.consistency_stage = "syntactic"
        self.candidate_records.clear()
        self.context_records.clear()
        self.accepted_candidate_order.clear()
        self.verification_candidate_order.clear()
        self.accepted_context_names.clear()
        self.rejected_context_names.clear()
        self.policy_note = ""
        self.active_goal_name = ""
        self.delta_geometry = None
        self.control_policy = None

    def record_candidate(
        self,
        candidate: str,
        *,
        record_id: str = "",
        accepted: bool,
        stage: str,
        reason: str = "",
        score: float = 0.0,
        error_type: str = "",
        metadata: Optional[Mapping[str, Any]] = None,
        verification_selected: bool = False,
    ) -> None:
        text = str(candidate or "")
        if not text:
            return
        record_key = self._record_key(
            text=text,
            record_id=record_id,
            metadata=metadata,
        )
        record = AdmissionRecord(
            key=record_key,
            kind="candidate",
            value=text,
            accepted=bool(accepted),
            stage=str(stage or ""),
            reason=str(reason or ""),
            score=float(score or 0.0),
            error_type=str(error_type or ""),
            metadata=dict(metadata or {}),
        )
        self.candidate_records[record_key] = record
        if accepted and record_key not in self.accepted_candidate_order:
            self.accepted_candidate_order.append(record_key)
        if (
            not accepted
            and record_key in self.accepted_candidate_order
        ):
            self.accepted_candidate_order.remove(record_key)
        if verification_selected and record_key not in self.verification_candidate_order:
            self.verification_candidate_order.append(record_key)
        if (
            not verification_selected
            and record_key in self.verification_candidate_order
        ):
            self.verification_candidate_order.remove(record_key)
        self.refresh_counts()

    def record_context(
        self,
        name: str,
        *,
        accepted: bool,
        stage: str,
        reason: str = "",
        value: str = "",
        metadata: Optional[Mapping[str, Any]] = None,
    ) -> None:
        key = str(name or "").strip()
        if not key:
            return
        record = AdmissionRecord(
            key=key,
            kind="context",
            value=str(value or ""),
            accepted=bool(accepted),
            stage=str(stage or ""),
            reason=str(reason or ""),
            metadata=dict(metadata or {}),
        )
        self.context_records[key] = record
        if accepted:
            if key not in self.accepted_context_names:
                self.accepted_context_names.append(key)
            if key in self.rejected_context_names:
                self.rejected_context_names.remove(key)
        else:
            if key not in self.rejected_context_names:
                self.rejected_context_names.append(key)
            if key in self.accepted_context_names:
                self.accepted_context_names.remove(key)

    @staticmethod
    def _record_key(
        *,
        text: str,
        record_id: str = "",
        metadata: Optional[Mapping[str, Any]] = None,
    ) -> str:
        explicit = str(record_id or "").strip()
        if explicit:
            return explicit
        meta = dict(metadata or {})
        provenance = str(
            meta.get("provenance_key")
            or meta.get("source_signature")
            or meta.get("source_key")
            or ""
        ).strip()
        ordinal = meta.get("generated_index", meta.get("ordered_index", ""))
        ordinal_text = str(ordinal).strip() if ordinal not in (None, "") else ""
        payload = "::".join(part for part in (text, provenance, ordinal_text) if part)
        if not payload:
            payload = text
        digest = hashlib.sha1(payload.encode("utf-8")).hexdigest()[:16]
        return f"candidate:{digest}"

    def refresh_counts(self) -> None:
        candidate_considered = int(len(self.candidate_records))
        candidate_admitted = int(
            sum(1 for record in self.candidate_records.values() if record.accepted)
        )
        candidate_rejected = int(max(0, candidate_considered - candidate_admitted))
        context_considered = int(len(self.context_records))
        context_admitted = int(
            sum(1 for record in self.context_records.values() if record.accepted)
        )
        context_rejected = int(max(0, context_considered - context_admitted))
        self.considered_count = int(candidate_considered + context_considered)
        self.admitted_count = int(candidate_admitted + context_admitted)
        self.rejected_count = int(candidate_rejected + context_rejected)

    def update_geometry_summary(
        self,
        *,
        stable_margin: float = 0.0,
        tail_distance: float = 0.0,
        dispersion: float = 0.0,
        resource_pressure: float = 0.0,
        consistency_stage: str = "",
    ) -> None:
        self.stable_margin = float(stable_margin or 0.0)
        self.tail_distance = float(tail_distance or 0.0)
        self.dispersion = float(dispersion or 0.0)
        self.resource_pressure = float(resource_pressure or 0.0)
        if consistency_stage:
            self.consistency_stage = str(consistency_stage)

    def summary(self) -> Dict[str, Any]:
        self.refresh_counts()
        candidate_considered = int(len(self.candidate_records))
        candidate_admitted = int(
            sum(1 for record in self.candidate_records.values() if record.accepted)
        )
        candidate_rejected = int(max(0, candidate_considered - candidate_admitted))
        context_considered = int(len(self.context_records))
        context_admitted = int(
            sum(1 for record in self.context_records.values() if record.accepted)
        )
        context_rejected = int(max(0, context_considered - context_admitted))
        return {
            "statement": str(self.statement),
            "cycle": int(self.cycle),
            "mode": str(self.mode),
            "considered": int(self.considered_count),
            "admitted": int(self.admitted_count),
            "rejected": int(self.rejected_count),
            "candidate_considered": int(candidate_considered),
            "candidate_admitted": int(candidate_admitted),
            "candidate_rejected": int(candidate_rejected),
            "context_considered": int(context_considered),
            "context_admitted": int(context_admitted),
            "context_rejected": int(context_rejected),
            "consistency_stage": str(self.consistency_stage),
            "last_action": str(self.last_action),
            "last_action_dim": str(self.last_action_dim),
            "stable_margin": float(self.stable_margin),
            "tail_distance": float(self.tail_distance),
            "dispersion": float(self.dispersion),
            "resource_pressure": float(self.resource_pressure),
            "accepted_candidate_keys": list(self.accepted_candidate_order),
            "verification_candidate_keys": list(self.verification_candidate_order),
            "accepted_context_names": list(self.accepted_context_names),
            "rejected_context_names": list(self.rejected_context_names),
        }


@dataclass
class DeltaGeometryState:
    """Controller-side geometry over recent delta vectors."""

    sigma: List[float] = field(default_factory=list)
    sigma_hat: List[float] = field(default_factory=list)
    covariance: List[List[float]] = field(default_factory=list)
    precision_matrix: List[List[float]] = field(default_factory=list)
    epsilon: float = 1.0
    hit_rate: float = 0.0
    tail_distance: float = 0.0
    stable_margin: float = 0.0
    dispersion: float = 0.0
    mean_vector: List[float] = field(default_factory=list)
    tail_mean_vector: List[float] = field(default_factory=list)
    last_distances: List[float] = field(default_factory=list)
    metric_mode: str = "whitened"
    source: str = "history"
    centroid_shift: List[float] = field(default_factory=list)
    measured_count: int = 0
    selector_vectors: Dict[str, List[float]] = field(default_factory=dict)
    regime_weights: List[float] = field(default_factory=list)
    regime_sigmas: List[List[float]] = field(default_factory=list)
    regime_covariances: List[List[List[float]]] = field(default_factory=list)
    regime_precision_matrices: List[List[List[float]]] = field(default_factory=list)


# ── Composite types (depend on types above) ───────────────────────────


@dataclass
class ReplanContext:
    """Accumulated across beam restarts within run_tree_search().

    Tracks failure history and solved subgoals so the planner can generate
    progressively better decompositions — gap-analysis replanning.
    """

    rounds: List[Tuple[int, List[SubgoalOutcome]]] = field(default_factory=list)
    solved_subgoals: List[str] = field(default_factory=list)
    seeded_subgoals: List[str] = field(default_factory=list)
    replan_count: int = 0
    seeded_replan: bool = False
    refiner_suggestions: List[str] = field(default_factory=list)
    active_obligation_ids: List[str] = field(default_factory=list)
    # Phase 2 of decide-refutation feedback. Each entry mirrors a row from
    # SearchSession.refuted_witness_ledger (see types.py:SearchSession).
    # Surfaced into the planner replan prompt so the LLM can re-derive a
    # different witness rather than re-emitting refuted ones. Honesty
    # contract: contains ONLY Lean verdicts (never system suggestions).
    refuted_witnesses: List[Dict[str, Any]] = field(default_factory=list)

    def add_round(self, round_num: int, outcomes: List[SubgoalOutcome]) -> None:
        self.rounds.append((round_num, outcomes))
        self.replan_count += 1
        for o in outcomes:
            if o.solved and o.statement not in self.solved_subgoals:
                self.solved_subgoals.append(o.statement)

    def failure_summary_text(self, max_rounds: int = 3) -> str:
        """Format human-readable context for prompt injection.

        When ``refuted_witnesses`` is non-empty, includes a dedicated
        section listing each refuted (statement, witness, evidence)
        triple so the planner can re-derive a different witness for the
        same goal. The section uses the literal heading ``Refuted
        witnesses (Lean verdicts):`` so prompt-template authors can
        anchor instruction text on the marker.
        """
        lines: List[str] = []
        recent = self.rounds[-max_rounds:]
        for round_num, outcomes in recent:
            lines.append(f"Round {round_num}:")
            for o in outcomes:
                if o.solved:
                    lines.append(
                        f"  + {o.statement[:200]} [SOLVED, score={o.score:.2f}]"
                    )
                else:
                    tag = f"FAILED ({o.error_type})" if o.error_type else "FAILED"
                    lines.append(
                        f"  - {o.statement[:200]} [{tag}, score={o.score:.2f}, attempts={o.attempts}]"
                    )
                    if o.error_summary:
                        lines.append(
                            f"    Error: {redact_internal_obligation_handles(o.error_summary)[:300]}"
                        )
        if self.solved_subgoals:
            lines.append(f"Already proven ({len(self.solved_subgoals)}):")
            for s in self.solved_subgoals:
                lines.append(f"  + {s[:200]}")
        if self.seeded_subgoals:
            lines.append(f"Recovered subgoals ({len(self.seeded_subgoals)}):")
            for s in self.seeded_subgoals:
                lines.append(f"  > {s[:200]}")
        if self.refiner_suggestions:
            lines.append(f"Refiner suggestions ({len(self.refiner_suggestions)}):")
            for s in self.refiner_suggestions:
                lines.append(f"  * {s[:300]}")
        if self.refuted_witnesses:
            # Truncate to the most recent 20 entries to bound prompt size.
            # Older entries remain in the SearchSession ledger for trace
            # observability; the planner only needs the recent slice.
            recent_refuted = self.refuted_witnesses[-20:]
            lines.append(
                f"Refuted witnesses (Lean verdicts) ({len(self.refuted_witnesses)}, showing last {len(recent_refuted)}):"
            )
            for entry in recent_refuted:
                witness_text = str(entry.get("witness_text", "") or "")[:160]
                shape = str(entry.get("shape", "") or "")
                evidence = str(entry.get("evidence", "") or "")[:200]
                count = int(entry.get("count", 1) or 1)
                count_tag = f" x{count}" if count > 1 else ""
                lines.append(
                    f"  ! [{shape}] witness `{witness_text}`{count_tag}"
                )
                if evidence:
                    lines.append(f"    Lean: {evidence}")
        if self.active_obligation_ids:
            lines.append(
                f"Active live obligations ({len(self.active_obligation_ids)}):"
            )
            lines.append("  ! internal obligation handles hidden from summaries")
        return "\n".join(lines)


@dataclass
class GoalScope:
    """Canonical per-goal scope shared by prompt construction and Lean checks."""

    materialized_context_text: str = "(none)"
    materialized_lemma_names: List[str] = field(default_factory=list)
    materialized_lemma_entries: List[Any] = field(default_factory=list)
    prompt_extra_blocks: List[str] = field(default_factory=list)
    prompt_extra_names: List[str] = field(default_factory=list)
    context_solved_names: List[str] = field(default_factory=list)
    proven_lemmas: List[Any] = field(default_factory=list)
    blocked_proven_names: List[str] = field(default_factory=list)
    recoverable_proven_lemmas: List[Any] = field(default_factory=list)
    hydrated_ref_cache: Dict[str, List[str]] = field(default_factory=dict)
    proven_prompt_suppressed: bool = False
    prompt_solved_support_only: bool = False

    def full_context_text(self) -> str:
        """Assemble full prompt context: library-first order.

        Extra blocks (Retrieved Mathlib, Local definitions) come FIRST,
        then materialized proven lemmas.  This ensures the LLM sees the
        authoritative API surface before any synthetic ``lemma_<hex>``
        entries.  When ``proven_prompt_suppressed`` is set, proven lemmas
        are omitted from the prompt (they remain available for Lean
        compilation via ``proven_lemmas``).
        """
        parts: List[str] = []
        for block in self.prompt_extra_blocks:
            text = str(block or "").strip()
            if text:
                parts.append(text)
        if (
            not self.proven_prompt_suppressed
            and self.materialized_context_text
            and self.materialized_context_text != "(none)"
        ):
            parts.append(self.materialized_context_text)
        return "\n\n".join(parts) if parts else "(none)"

    def all_context_lemma_names(self) -> List[str]:
        return list(
            dict.fromkeys(
                [
                    *[str(name).strip() for name in self.materialized_lemma_names],
                    *[str(name).strip() for name in self.prompt_extra_names],
                ]
            )
        )

    def prompt_only_context_lemma_names(self) -> List[str]:
        materialized = {str(name).strip() for name in self.materialized_lemma_names}
        return list(
            dict.fromkeys(
                [
                    str(name).strip()
                    for name in self.prompt_extra_names
                    if str(name).strip() and str(name).strip() not in materialized
                ]
            )
        )

    def executable_context_lemma_names(self) -> List[str]:
        return list(
            dict.fromkeys([str(name).strip() for name in self.materialized_lemma_names])
        )

    def executable_context_lemma_entries(self) -> List[Any]:
        seen: set[str] = set()
        entries: List[Any] = []
        for entry in self.materialized_lemma_entries:
            name = str(getattr(entry, "name", "") or "").strip()
            if not name or name in seen:
                continue
            seen.add(name)
            entries.append(entry)
        return entries

    def executable_solved_support_names(self) -> List[str]:
        return list(
            dict.fromkeys(
                str(name).strip()
                for name in self.context_solved_names
                if str(name).strip()
            )
        )

    def executable_bridge_decl_names(self) -> List[str]:
        solved = set(self.executable_solved_support_names())
        return list(
            dict.fromkeys(
                str(name).strip()
                for name in self.materialized_lemma_names
                if str(name).strip() and str(name).strip() not in solved
            )
        )


@dataclass(frozen=True)
class TheoremScaffold:
    """Planner-authored theorem-level execution scaffold.

    Captures the global route that a stronger planner model can hand to the
    prover: the expected final shape, selected branch, validated bridge claims,
    and assembly steps that explain how those claims close the root theorem.
    """

    route_summary: str = ""
    final_shape: str = ""
    selected_branch: str = ""
    assembly_steps: List[str] = field(default_factory=list)
    critical_claims: List["ValidatedSubgoal"] = field(default_factory=list)
    support_claims: List["ValidatedSubgoal"] = field(default_factory=list)
    confidence: float = 0.0
    raw_critical_claims: List[str] = field(default_factory=list)
    raw_support_claims: List[str] = field(default_factory=list)
    sketch_text: str = ""
    sketch_claims: List["ValidatedSubgoal"] = field(default_factory=list)
    planner_critical_claims: List["ValidatedSubgoal"] = field(default_factory=list)
    planner_support_claims: List["ValidatedSubgoal"] = field(default_factory=list)
    canonical_claim_sources: Dict[str, str] = field(default_factory=dict)

    @property
    def validated_claims(self) -> List["ValidatedSubgoal"]:
        return [*self.critical_claims, *self.support_claims]

    @property
    def planner_validated_claims(self) -> List["ValidatedSubgoal"]:
        return [*self.planner_critical_claims, *self.planner_support_claims]

    @classmethod
    def refresh_from(cls, workset: Any) -> "TheoremScaffold":
        """Rebuild the theorem-scaffold view from the canonical RootWorkset."""
        nodes = _workset_nodes(workset)
        support_nodes = _workset_support_nodes(workset, nodes)
        critical_nodes = [
            node
            for node in nodes
            if _workset_enum_value(getattr(node, "kind", ""))
            in {"bridge_lemma", "open_root_hole", "scaffold_slot"}
            and _workset_enum_value(getattr(node, "status", "")) != "rejected"
            and _workset_node_statement(node)
        ]

        def _subgoal(node: Any, role: str) -> "ValidatedSubgoal":
            statement = _workset_node_statement(node)
            metadata = _workset_metadata(node)
            return ValidatedSubgoal(
                original_statement=statement,
                statement=statement,
                obligation_id=str(getattr(node, "name", "") or "").strip(),
                source_kind=f"workset:{_workset_enum_value(getattr(node, 'kind', ''))}",
                source_role=role,
                dependency_ids=_workset_str_list(metadata.get("dependency_ids", [])),
                proof_plan=str(metadata.get("proof_plan", "") or ""),
            )

        critical_claims = [_subgoal(node, "critical") for node in critical_nodes]
        support_claims = [_subgoal(node, "support") for node in support_nodes]
        canonical_sources = {
            _workset_node_statement(node): str(getattr(node, "name", "") or "").strip()
            for node in [*critical_nodes, *support_nodes]
            if _workset_node_statement(node)
        }
        route_summary = (
            f"workset refresh: {len(nodes)} node(s), "
            f"{len(support_nodes)} root-support node(s)"
        )
        return cls(
            route_summary=route_summary,
            final_shape=_workset_root_statement(workset, nodes),
            selected_branch="workset",
            critical_claims=critical_claims,
            support_claims=support_claims,
            raw_critical_claims=[
                _workset_node_statement(node) for node in critical_nodes
            ],
            raw_support_claims=[
                _workset_node_statement(node) for node in support_nodes
            ],
            canonical_claim_sources=canonical_sources,
        )


@dataclass(frozen=True)
class ScaffoldSlotSpec:
    """Planner-authored assembly intent for a single proof obligation slot.

    Advisory only. Authoritative local hypotheses and binder state come
    exclusively from Lean-derived CompiledScaffoldSlot instances.
    """

    slot_id: str = ""
    slot_purpose: str = ""
    closure_kind: str = ""
    preferred_owner: str = ""
    dependency_ids: List[str] = field(default_factory=list)
    claim_statement: str = ""


@dataclass(frozen=True)
class ExecutableScaffoldTemplate:
    """Planner-authored assembly template (advisory layer only).

    Captures slot ids, dependencies, assembly order, slot purpose,
    preferred owner, and closure kind.  Must not carry authoritative
    local hypotheses or binder state — those come from CompiledScaffoldState.
    """

    assembly_template: str = ""
    slots: List["ScaffoldSlotSpec"] = field(default_factory=list)
    dependencies: Dict[str, List[str]] = field(default_factory=dict)
    closure_kind: str = ""
    preferred_owner: str = ""


@dataclass(frozen=True)
class CompiledScaffoldSlot:
    """Lean-derived authoritative state for one proof obligation slot.

    All hypothesis and binder information comes from the Lean checker,
    not from planner text.  status: pending | solved | failed | skipped
    """

    slot_id: str = ""
    hole_id: str = ""
    target: str = ""
    hypotheses: List[str] = field(default_factory=list)
    binders: str = ""
    dependency_ids: List[str] = field(default_factory=list)
    scaffold_claim_statement: str = ""
    source_claim_statement: str = ""
    # True when `source_claim_statement` comes from the authoritative root
    # contract / scaffold source claim, not from a synthetic fallback or a
    # test helper copying `target`. Execution should prefer that surface even
    # when it happens to textually match `target`.
    source_claim_authoritative: bool = False
    source_helper_name: str = ""
    preferred_owner: str = ""
    closure_kind: str = ""
    status: str = "pending"
    proof: str = ""
    failure_fingerprints: List[str] = field(default_factory=list)
    attempt_count: int = 0
    # Closure-gap A3 (deeper fix): preserve the full Lean failure
    # preview (not the 64-char fingerprint) from the most recent failed
    # attempt on this slot. ``failure_fingerprints`` are short hashes
    # used as predicates ("did we have a plan_locked_exhausted failure
    # before?"); the deeper structural fix is to also carry the
    # actionable Lean output forward so the refiner / repair prompts
    # can surface PRIOR failure context, not just the current attempt's
    # error. Populated at the executor's failure-record point;
    # consumed by ``_plan_locked_refine_tactic`` and other prompt
    # builders when ``attempt_count > 0``.
    last_failure_preview: str = ""
    # Number of local hypotheses Lean lifted into the slot's target as
    # leading Pi-binders (e.g. when `have h : T := by refine ?_` precedes
    # this slot's hole, `h` is lifted into the goal as `∀ h : T, body`).
    # When stitching the standalone proof back into the scaffold's have-
    # binding, the proof must be specialized via `(proof) _ _ ... _` with
    # `local_argc` underscores. Without this, the substituted proof has
    # the wrong intro count and `introN` fails — see live trace
    # 2001_a1_16apr_14.jsonl: slot_2 solved standalone, refresh failed
    # with compile_stopped because proof was stitched raw with
    # local_argc=0 hardcoded. Propagated from RootContractHole.local_argc.
    local_argc: int = 0
    # Planner-proposed Lean tactic (``by <tactics>``) that closes this slot's
    # target. Propagated from ``ValidatedSubgoal.proof_plan`` when the
    # scaffold slot derives from a sketch HAVE claim. The slot executor
    # tries this tactic verbatim before invoking generic free-form proving.
    proof_plan: str = ""
    # Source role from the checked root contract. Root-like pending claims are
    # still executable slots, but they must retain terminal root-closure
    # identity so the executor can stop once Lean verifies the root.
    role: str = "pending_claim"
    closes_root: bool = False
    root_statement: str = ""


@dataclass
class CompiledScaffoldState:
    """Session-owned authoritative execution state for a compiled scaffold.

    Owned by the active search session.  GoalContext mirrors only the
    minimal handles (scaffold_id, slot_id) needed by prompt construction
    and candidate filtering.
    """

    scaffold_id: str = ""
    root_statement: str = ""
    slots: List[CompiledScaffoldSlot] = field(default_factory=list)
    current_assembly: str = ""
    origin_theorem_scaffold: Optional["TheoremScaffold"] = None
    compile_ok: bool = False
    executor_round: int = 0
    no_progress_rounds: int = 0
    abandon_reason: str = ""
    abandonment_fingerprint: str = ""
    refresh_error_type: str = ""
    refresh_fallback_reason: str = ""
    refresh_diagnostic_preview: str = ""
    refresh_returncode: int = 0
    first_slot_close_time: Optional[float] = None
    first_root_proof_time: Optional[float] = None
    error_fingerprint_counts: Dict[str, int] = field(default_factory=dict)

    @classmethod
    def refresh_from(cls, workset: Any) -> "CompiledScaffoldState":
        """Rebuild the compiled-scaffold execution view from RootWorkset nodes."""
        nodes = _workset_nodes(workset)
        root_statement = _workset_root_statement(workset, nodes)
        root_node_metadata = {}
        for node in nodes:
            if _workset_enum_value(getattr(node, "kind", "")) == "root_claim":
                root_node_metadata = _workset_metadata(node)
                break
        slot_nodes = [
            node
            for node in nodes
            if _workset_enum_value(getattr(node, "kind", "")) in _WORKSET_SLOT_KINDS
        ]
        slot_nodes.sort(
            key=lambda node: (
                _workset_int(_workset_metadata(node).get("ordinal", 0), 0),
                str(getattr(node, "name", "") or ""),
            )
        )

        slots: List[CompiledScaffoldSlot] = []
        for idx, node in enumerate(slot_nodes, start=1):
            metadata = _workset_metadata(node)
            name = str(getattr(node, "name", "") or "").strip() or f"slot_{idx}"
            status_value = _workset_enum_value(getattr(node, "status", ""))
            if status_value in _WORKSET_SOLVED_STATUSES:
                slot_status = "solved"
            elif status_value == "rejected":
                slot_status = "failed"
            else:
                slot_status = str(metadata.get("slot_status", "") or "pending")
            target = (
                str(metadata.get("execution_statement", "") or "").strip()
                or str(metadata.get("goal_target", "") or "").strip()
                or _workset_node_statement(node)
            )
            slots.append(
                CompiledScaffoldSlot(
                    slot_id=str(metadata.get("slot_id", "") or name),
                    hole_id=str(metadata.get("hole_id", "") or name),
                    target=target,
                    hypotheses=_workset_str_list(metadata.get("hypotheses", [])),
                    binders=str(metadata.get("binders", "") or ""),
                    dependency_ids=_workset_str_list(metadata.get("dependency_ids", [])),
                    scaffold_claim_statement=str(
                        metadata.get("scaffold_claim_statement", "") or ""
                    ),
                    source_claim_statement=(
                        str(metadata.get("source_claim_statement", "") or "").strip()
                        or _workset_node_statement(node)
                    ),
                    source_claim_authoritative=bool(
                        metadata.get("source_claim_authoritative", False)
                    ),
                    source_helper_name=str(metadata.get("source_helper_name", "") or ""),
                    preferred_owner=str(metadata.get("preferred_owner", "") or ""),
                    closure_kind=str(metadata.get("closure_kind", "") or ""),
                    status=slot_status,
                    proof=str(metadata.get("proof", "") or ""),
                    failure_fingerprints=_workset_str_list(
                        metadata.get("failure_fingerprints", [])
                    ),
                    attempt_count=_workset_int(metadata.get("attempt_count", 0), 0),
                    local_argc=_workset_int(metadata.get("local_argc", 0), 0),
                    proof_plan=str(metadata.get("proof_plan", "") or ""),
                    role=str(metadata.get("slot_role", "") or metadata.get("role", "") or "pending_claim"),
                    closes_root=bool(metadata.get("closes_root", False)),
                    root_statement=str(
                        metadata.get("root_statement", "") or root_statement or ""
                    ),
                )
            )

        scaffold_id = str(root_node_metadata.get("scaffold_id", "") or "").strip()
        if not scaffold_id:
            scaffold_id = "workset:" + _workset_fingerprint(
                root_statement,
                [
                    (
                        slot.slot_id,
                        slot.target,
                        slot.status,
                    )
                    for slot in slots
                ],
            )
        return cls(
            scaffold_id=scaffold_id,
            root_statement=root_statement,
            slots=slots,
            current_assembly=str(root_node_metadata.get("current_assembly", "") or ""),
            origin_theorem_scaffold=TheoremScaffold.refresh_from(workset),
            compile_ok=bool(
                root_node_metadata.get("compile_ok", False)
                or (slots and all(slot.status != "failed" for slot in slots))
            ),
            executor_round=_workset_int(root_node_metadata.get("executor_round", 0), 0),
            no_progress_rounds=_workset_int(
                root_node_metadata.get("no_progress_rounds", 0), 0
            ),
            abandon_reason=str(root_node_metadata.get("abandon_reason", "") or ""),
            abandonment_fingerprint=str(
                root_node_metadata.get("abandonment_fingerprint", "") or ""
            ),
        )


@dataclass(frozen=True)
class CompositionSummary:
    """Typed composition outcome/telemetry summary."""

    calls: int = 0
    attempts: int = 0
    successes: int = 0
    failures: int = 0
    llm_errors: int = 0
    no_candidate_rounds: int = 0
    check_exceptions: int = 0
    manual_ready: bool = False
    auto_ready: bool = False
    support_fingerprint: str = ""
    solved_helper_count: int = 0
    bridge_helper_count: int = 0
    requested_solved_count: int = 0
    materialized_solved_count: int = 0
    solved_to_materialized_gap: int = 0
    solved_to_materialized_ratio: float = 1.0
    audit_deferred: bool = False
    audit_obligations_enqueued: int = 0
    audit_obligations_duplicate: int = 0
    audit_obligations_filtered: int = 0
    audit_obligations_backpressured: int = 0
    audit_closing_verdict: Optional[bool] = None
    audit_status: str = ""

    @staticmethod
    def _safe_int(value: Any) -> int:
        try:
            return int(value or 0)
        except Exception:
            return 0

    @staticmethod
    def _safe_float(value: Any, default: float = 0.0) -> float:
        try:
            return float(value)
        except Exception:
            return float(default)

    @staticmethod
    def _safe_optional_bool(value: Any) -> Optional[bool]:
        if value is None:
            return None
        if isinstance(value, bool):
            return value
        if isinstance(value, (int, float)):
            return bool(value)
        if isinstance(value, str):
            lowered = value.strip().lower()
            if lowered in {"true", "1", "yes", "y"}:
                return True
            if lowered in {"false", "0", "no", "n"}:
                return False
            if lowered in {"", "none", "null"}:
                return None
        return bool(value)

    @staticmethod
    def _safe_bool(value: Any, default: bool = False) -> bool:
        parsed = CompositionSummary._safe_optional_bool(value)
        if parsed is None:
            return bool(default)
        return bool(parsed)

    @classmethod
    def from_metrics(
        cls,
        metrics: Optional[Mapping[str, Any]],
        *,
        manual_ready: bool = False,
        auto_ready: bool = False,
        support_fingerprint: str = "",
        solved_helper_count: int = 0,
        bridge_helper_count: int = 0,
    ) -> "CompositionSummary":
        source: Any = metrics or {}
        nested: Any = None
        if isinstance(metrics, Mapping):
            nested = metrics.get("composition")

        _MISSING = object()  # sentinel to distinguish 0/False from absent

        def _read_nested(name: str) -> Any:
            if isinstance(nested, cls):
                return getattr(nested, name, _MISSING)
            if isinstance(nested, Mapping) and name in nested:
                return nested[name]
            return _MISSING

        def _read_source(name: str) -> Any:
            if isinstance(source, Mapping):
                if name in source:
                    return source[name]
                return _MISSING
            val = getattr(source, name, _MISSING)
            return val

        def _read(
            name: str,
            legacy_name: Optional[str] = None,
            default: Any = 0,
            fallback_names: tuple[str, ...] = (),
        ) -> Any:
            legacy_names = tuple(
                str(alias).strip()
                for alias in (legacy_name, *fallback_names)
                if str(alias or "").strip()
            )
            for legacy_alias in legacy_names:
                legacy_value = _read_source(legacy_alias)
                if legacy_value is not _MISSING:
                    return legacy_value
            nested_value = _read_nested(name)
            if nested_value is not _MISSING:
                return nested_value
            source_value = _read_source(name)
            if source_value is not _MISSING:
                return source_value
            for legacy_alias in legacy_names:
                nested_legacy_value = _read_nested(legacy_alias)
                if nested_legacy_value is not _MISSING:
                    return nested_legacy_value
            return default

        attempts = cls._safe_int(_read("attempts", "composition_attempts", 0))
        successes = cls._safe_int(_read("successes", "composition_successes", 0))
        return cls(
            calls=cls._safe_int(_read("calls", "composition_calls", attempts)),
            attempts=attempts,
            successes=successes,
            failures=cls._safe_int(
                _read(
                    "failures",
                    "composition_failures",
                    max(0, attempts - successes),
                )
            ),
            llm_errors=cls._safe_int(_read("llm_errors", "composition_llm_errors", 0)),
            no_candidate_rounds=cls._safe_int(
                _read("no_candidate_rounds", "composition_no_candidate_rounds", 0)
            ),
            check_exceptions=cls._safe_int(
                _read("check_exceptions", "composition_check_exceptions", 0)
            ),
            manual_ready=cls._safe_bool(
                _read("manual_ready", "composition_manual_ready", default=manual_ready),
                default=manual_ready,
            ),
            auto_ready=cls._safe_bool(
                _read("auto_ready", "composition_auto_ready", default=auto_ready),
                default=auto_ready,
            ),
            support_fingerprint=str(
                _read(
                    "support_fingerprint",
                    "composition_support_fingerprint",
                    support_fingerprint,
                )
                or ""
            ),
            solved_helper_count=cls._safe_int(
                _read(
                    "solved_helper_count",
                    "composition_solved_helper_count",
                    solved_helper_count,
                )
            ),
            bridge_helper_count=cls._safe_int(
                _read(
                    "bridge_helper_count",
                    "composition_bridge_helper_count",
                    bridge_helper_count,
                )
            ),
            requested_solved_count=cls._safe_int(
                _read(
                    "ready_solved_count",
                    "composition_ready_solved_count",
                    0,
                    fallback_names=(
                        "requested_solved_count",
                        "composition_requested_solved_count",
                    ),
                )
            ),
            materialized_solved_count=cls._safe_int(
                _read(
                    "materialized_ready_solved_count",
                    "composition_materialized_ready_solved_count",
                    0,
                    fallback_names=(
                        "materialized_solved_count",
                        "composition_materialized_solved_count",
                    ),
                )
            ),
            solved_to_materialized_gap=cls._safe_int(
                _read(
                    "ready_solved_materialization_gap",
                    "composition_ready_solved_materialization_gap",
                    0,
                    fallback_names=(
                        "solved_to_materialized_gap",
                        "composition_solved_to_materialized_gap",
                    ),
                )
            ),
            solved_to_materialized_ratio=cls._safe_float(
                _read(
                    "ready_solved_materialization_ratio",
                    "composition_ready_solved_materialization_ratio",
                    1.0,
                    fallback_names=(
                        "solved_to_materialized_ratio",
                        "composition_solved_to_materialized_ratio",
                    ),
                ),
                default=1.0,
            ),
            audit_deferred=cls._safe_bool(
                _read(
                    "audit_deferred",
                    "composition_audit_deferred",
                    False,
                ),
                default=False,
            ),
            audit_obligations_enqueued=cls._safe_int(
                _read(
                    "audit_obligations_enqueued",
                    "composition_audit_obligations_enqueued",
                    0,
                )
            ),
            audit_obligations_duplicate=cls._safe_int(
                _read(
                    "audit_obligations_duplicate",
                    "composition_audit_obligations_duplicate",
                    0,
                )
            ),
            audit_obligations_filtered=cls._safe_int(
                _read(
                    "audit_obligations_filtered",
                    "composition_audit_obligations_filtered",
                    0,
                )
            ),
            audit_obligations_backpressured=cls._safe_int(
                _read(
                    "audit_obligations_backpressured",
                    "composition_audit_obligations_backpressured",
                    0,
                )
            ),
            audit_closing_verdict=cls._safe_optional_bool(
                _read(
                    "audit_closing_verdict",
                    "composition_audit_closing_verdict",
                    None,
                )
            ),
            audit_status=str(
                _read(
                    "audit_status",
                    "composition_audit_status",
                    "",
                )
                or ""
            ),
        )

    @property
    def success(self) -> bool:
        return int(self.successes) > 0

    @property
    def checked_candidate(self) -> bool:
        return int(self.attempts) > 0

    @property
    def context_ready(self) -> bool:
        return bool(self.manual_ready)

    @property
    def composable_ready(self) -> bool:
        return bool(self.auto_ready)

    @property
    def bridge_only_ready(self) -> bool:
        return bool(self.context_ready and not self.composable_ready)

    @property
    def ready_solved_count(self) -> int:
        return int(self.requested_solved_count)

    @property
    def materialized_ready_solved_count(self) -> int:
        return int(self.materialized_solved_count)

    @property
    def ready_solved_materialization_gap(self) -> int:
        return int(self.solved_to_materialized_gap)

    @property
    def ready_solved_materialization_ratio(self) -> float:
        return float(self.solved_to_materialized_ratio)

    @property
    def controller_failure(self) -> bool:
        return any(
            int(count) > 0
            for count in (
                self.failures,
                self.no_candidate_rounds,
                self.check_exceptions,
            )
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "calls": int(self.calls),
            "attempts": int(self.attempts),
            "successes": int(self.successes),
            "failures": int(self.failures),
            "llm_errors": int(self.llm_errors),
            "no_candidate_rounds": int(self.no_candidate_rounds),
            "check_exceptions": int(self.check_exceptions),
            "manual_ready": bool(self.manual_ready),
            "auto_ready": bool(self.auto_ready),
            "context_ready": bool(self.context_ready),
            "composable_ready": bool(self.composable_ready),
            "bridge_only_ready": bool(self.bridge_only_ready),
            "support_fingerprint": str(self.support_fingerprint),
            "solved_helper_count": int(self.solved_helper_count),
            "bridge_helper_count": int(self.bridge_helper_count),
            "ready_solved_count": int(self.ready_solved_count),
            "materialized_ready_solved_count": int(
                self.materialized_ready_solved_count
            ),
            "ready_solved_materialization_gap": int(
                self.ready_solved_materialization_gap
            ),
            "ready_solved_materialization_ratio": float(
                self.ready_solved_materialization_ratio
            ),
            "requested_solved_count": int(self.requested_solved_count),
            "materialized_solved_count": int(self.materialized_solved_count),
            "solved_to_materialized_gap": int(self.solved_to_materialized_gap),
            "solved_to_materialized_ratio": float(self.solved_to_materialized_ratio),
            "audit_deferred": bool(self.audit_deferred),
            "audit_obligations_enqueued": int(self.audit_obligations_enqueued),
            "audit_obligations_duplicate": int(self.audit_obligations_duplicate),
            "audit_obligations_filtered": int(self.audit_obligations_filtered),
            "audit_obligations_backpressured": int(
                self.audit_obligations_backpressured
            ),
            "audit_closing_verdict": self.audit_closing_verdict,
            "audit_status": str(self.audit_status),
        }


@dataclass
class CompositionSetup:
    """Phase 2a setup bundle for ``_attempt_composition_outcome``.

    Populated by ``Orchestrator._build_composition_setup`` — an
    intentionally pure/read-only helper that lifts the opening 70-ish
    lines of ``_attempt_composition_outcome`` into a single call. See
    architecture_mapping_for_analysis/proof_graph_first_refactor_plan_2026-04-23.md
    §4 Phase 2a.

    Notes:
    - ``selected_prover_client`` holds a live client handle. Code must
      reference it by identity or by ``selected_prover_role``; never
      deep-compare or serialize this field.
    - ``composition_ctx`` is a freshly built GoalContext; the outer
      function is free to mutate it. ``support_summary`` is a template
      for ``_finish()`` to merge counters into via ``dataclasses.replace``.
    """

    composition_ctx: "GoalContext"
    root_support: "RootSupportSnapshot"
    support_summary: "CompositionSummary"
    selected_prover_client: Any
    selected_prover_role: str
    composition_failure_state_key: str
    strategy_guidance: Any
    temp: float
    max_rounds: int
    failure_aggregation_enabled: bool
    root_support_ready: bool


@dataclass
class GoalContext:
    last_parse: Optional[LeanParseResult] = None
    context_text: str = ""
    context_lemma_names: List[str] = field(default_factory=list)
    # Subset of self.solved to inject into prompt/Lean context for this goal.
    # Bounded via search.max_context_solved_lemmas to avoid context blowups.
    context_solved_names: List[str] = field(default_factory=list)
    # Per-goal proven-lemma retrieval results (avoid cross-goal contamination).
    proven_lemmas: List[Any] = field(default_factory=list)
    # Canonical scope object. Legacy fields above are mirrored from this.
    scope: GoalScope = field(default_factory=GoalScope)
    admitted_state: AdmittedState = field(default_factory=AdmittedState)
    goal_embedding: Optional[List[float]] = None
    active_goal: Optional[StrategyGoal] = None
    policy: Optional[MasterPolicy] = None
    policy_cycle: int = 0
    failed_strategies: List[str] = field(default_factory=list)
    initial_goal_count: Optional[int] = None
    goal_state_text: str = ""
    goal_state_features: Optional[GoalStateFeatures] = None
    # Retrieval diagnostics for observability
    retrieval_stats: Optional[Dict[str, Any]] = None
    # Feature map for LTR (lemma_name -> feature dict)
    retrieval_features: Optional[Dict[str, Dict[str, float]]] = None
    # Subgoal decomposition depth (0 = root theorem)
    depth: int = 0
    # Directed hints from refiner/planner for this specific goal.
    hints: List[DirectedHint] = field(default_factory=list)
    # Accumulated failure summaries from previous prove_statement rounds.
    failure_round_summaries: List[FailureRoundSummary] = field(default_factory=list)
    # Bounded same-target retries after a precheck-only collapse so the next
    # prover turn can see the synthesized Lean diagnostics immediately.
    precheck_feedback_retry_counts: Dict[str, int] = field(default_factory=dict)
    # Unknown identifiers observed for this goal; filter future candidates that reuse them.
    blocked_identifiers: List[str] = field(default_factory=list)
    # Soft-block strike counts for durable in-scope helpers that hit unknown_identifier.
    # Hard-block only after repeated strikes (or immediately when the helper is not durable).
    unknown_identifier_strikes: Dict[str, int] = field(default_factory=dict)
    # Failed proof hashes observed for this goal; filter exact retries.
    failed_proof_hashes: List[str] = field(default_factory=list)
    # Goal-frontier contract failures observed for this goal (e.g. repeated
    # binder-shape families on the current active goal). Used to suppress
    # structurally redundant retries that differ only in proof tail details.
    failed_goal_contract_signatures: List[str] = field(default_factory=list)
    failed_goal_contract_counts: Dict[str, int] = field(default_factory=dict)
    # Best-known failure previews keyed by proof hash.
    failed_error_by_hash: Dict[str, str] = field(default_factory=dict)
    # Best-known error types keyed by proof hash.
    failed_error_type_by_hash: Dict[str, str] = field(default_factory=dict)
    # Sorry taxonomy memory (non-binding hints/avoidance signals).
    sorry_hints: List[str] = field(default_factory=list)
    sorry_avoidance_tags: List[str] = field(default_factory=list)
    # Synthetic lemma names that appeared in failed proofs for this goal.
    # Used to penalize candidates that re-reference these same names.
    failed_synth_lemma_refs: set = field(default_factory=set)
    # Per-name failure counts for escalating synth penalty (2^(count-1) multiplier).
    failed_synth_lemma_ref_counts: Dict[str, int] = field(default_factory=dict)
    # Synthetic helper lemmas that stayed in scope but failed semantically on
    # this goal (for example `type_mismatch` / `unsolved_goals` / `tactic_failed`).
    failed_semantic_helper_refs: set = field(default_factory=set)
    # Per-name semantic failure counts for goal-local helper retry suppression.
    failed_semantic_helper_ref_counts: Dict[str, int] = field(default_factory=dict)
    # Skeleton proving is structural work and should not be blocked by
    # replan-reserve bookkeeping for generic refinement.
    refiner_budget_lane: str = "refine"
    # Stable owner label for human-facing logs produced inside this prove call.
    log_scope: str = ""
    # Active contract/obligation metadata for this specific proving task.
    active_obligation_id: str = ""
    active_obligation_roles: List[str] = field(default_factory=list)
    active_obligation_sources: List[str] = field(default_factory=list)
    active_dependency_ids: List[str] = field(default_factory=list)
    # Per-invocation proof-check counters, separate from global run metrics.
    check_stats: ProofCheckStats = field(default_factory=ProofCheckStats)
    # Direction critic state
    statement_attempt_idx: int = 0  # How many prove rounds on this statement
    dominant_remaining_goal: str = ""  # Most frequent unsolved goal across rounds
    # Refiner pattern feedback: which patterns were shown to the prover
    injected_refiner_patterns: List[str] = field(default_factory=list)
    # Compact failed-candidate batch summary shown to the refiner.
    refine_batch_feedback: str = ""
    # Soft strategy-advisor note reused across prompt lanes for this goal.
    strategy_advisor_note: str = ""
    strategy_advisor_reason: str = ""
    strategy_advisor_basis: str = ""
    strategy_advisor_signal: str = ""
    strategy_advisor_payload: str = ""
    # Planner-authored theorem scaffold shared across prover/refiner/root-contract
    # lanes so global theorem architecture remains explicit instead of being
    # collapsed into generic sketch prose.
    theorem_scaffold: Optional[TheoremScaffold] = None
    # Tool-augmented proving evidence persisted across generation retries.
    tool_checked_decls: Dict[str, str] = field(default_factory=dict)
    tool_searched_decls: Dict[str, str] = field(default_factory=dict)
    tool_verified_decl_plans: List["VerifiedDeclApplication"] = field(
        default_factory=list
    )
    # Active root contract metadata when root proving is constrained to
    # discharge a checked decomposition scaffold instead of improvising.
    root_contract_id: str = ""
    root_contract_support_fingerprint: str = ""
    root_contract_mode: str = ""
    root_contract_scaffold: str = ""
    root_contract_hole_id: str = ""
    # ── Executable scaffold executor handles (Phase 1) ─────────────────────
    # Minimal mirrors of session-owned CompiledScaffoldState for prompt
    # construction and candidate filtering.  The authoritative state lives
    # in the search session; these are compatibility handles only.
    active_compiled_scaffold_id: str = ""
    current_slot_id: str = ""
    compiled_scaffold_state: Optional["CompiledScaffoldState"] = None
    # Mapping from scaffold-local lifted binder names (for example
    # h_root_contract_N) to materialized helper lemma names for the current
    # execution surface. These local binders are not available when a slot is
    # proved against its unlifted source claim.
    scaffold_local_aliases: Dict[str, str] = field(default_factory=dict)
    abandonment_fingerprint: str = ""
    abandonment_reason: str = ""
    executor_round_count: int = 0


@dataclass(frozen=True)
class VerifiedDeclApplication:
    """Lean-verified declaration application plan for one concrete goal."""

    decl_name: str
    proof_stub: str
    remaining_goals: List[str] = field(default_factory=list)
    instantiated_target: str = ""
    statement: str = ""
    error_kind: str = ""
    frontier_delta_score: float = 0.0


@dataclass
class ValidatedSubgoal:
    """A validated subgoal or sketch claim with preserved source identity."""

    original_statement: str
    statement: str
    admission_mode: str = ""
    obligation_id: str = ""
    source_kind: str = ""
    source_role: str = ""
    dependency_ids: List[str] = field(default_factory=list)
    # Executable tactic the planner proposed to close this claim. When
    # ``source_kind == "sketch_have"``, ``proof_plan`` carries the Lean tactic
    # block (``by <tactics>``) emitted alongside ``have_claim`` in the sketch
    # JSON response. Downstream the scaffold slot executor tries this
    # tactic verbatim before invoking the generic free-form prover, so the
    # planner's answer is actually executed rather than re-derived.
    proof_plan: str = ""


@dataclass
class ProofSketchArtifact:
    """Upgradeable cached proof-sketch payload."""

    sketch_text: str = ""
    raw_have_claims: List[str] = field(default_factory=list)
    validated_haves: List["ValidatedSubgoal"] = field(default_factory=list)
    validated_ready: bool = False
    structural_signal: str = ""
    structural_payload: str = ""
    structural_source: str = ""


@dataclass(frozen=True)
class MissingObligation:
    """Planner-audited missing root-bridge proposition."""

    statement: str
    rationale: str = ""
    parsed_ok: bool = False
    normalized_statement: str = ""


@dataclass(frozen=True)
class RootSupportAudit:
    """Semantic audit of whether current root support can close the theorem."""

    audit_fingerprint: str = ""
    support_fingerprint: str = ""
    controller_key: str = ""
    status: str = "skipped"
    closing: Optional[bool] = None
    rationale: str = ""
    missing_obligations: List[MissingObligation] = field(default_factory=list)
    raw_response: str = ""
    prompt_hash: str = ""
    from_cache: bool = False
    obligations_enqueued: int = 0
    obligations_duplicate: int = 0
    obligations_filtered: int = 0
    obligations_backpressured: int = 0

    @property
    def sufficient(self) -> bool:
        return bool(self.closing is True or self.status == "sufficient")

    @property
    def insufficient(self) -> bool:
        return bool(self.closing is False or self.status == "insufficient")


class RootIntegrationPhase(enum.Enum):
    """Phases for the root-integration controller."""

    EXPLORE = "explore"
    ROOT_FOCUS_PENDING = "root_focus_pending"
    ROOT_FOCUS = "root_focus"


@dataclass(frozen=True)
class RootSupportSnapshot:
    """Canonical root-support context shared by prompting and Lean checks."""

    scope: GoalScope = field(default_factory=GoalScope)
    materialized_names: List[str] = field(default_factory=list)
    solved_names: List[str] = field(default_factory=list)
    bridge_names: List[str] = field(default_factory=list)
    runtime_bridge_names: List[str] = field(default_factory=list)
    prompt_text: str = "(none)"
    solved_prompt_text: str = "(none)"
    bridge_prompt_text: str = "(none)"
    runtime_bridge_prompt_text: str = "(none)"
    controller_key: str = ""
    fingerprint: str = ""

    @property
    def ready(self) -> bool:
        # Root composition is viable whenever the canonical materialized support
        # exposes at least one Lean-visible helper, regardless of whether that
        # helper came from a solved subgoal or a retrieved bridge lemma.
        if self.materialized_names:
            return True
        return bool(getattr(self.scope, "materialized_lemma_names", None))

    @property
    def has_materialized_solved_support(self) -> bool:
        # Auto-composition should only treat solved helpers as available when
        # they actually survived canonical materialization into Lean-visible
        # support, not merely because a solved lemma exists elsewhere in state.
        if self.solved_names:
            return True
        return bool(getattr(self.scope, "context_solved_names", None))

    @property
    def usable_support_names(self) -> List[str]:
        names = list(self.solved_names or [])
        if not names:
            names = list(getattr(self.scope, "context_solved_names", []) or [])
        return list(
            dict.fromkeys(str(name).strip() for name in names if str(name).strip())
        )

    @property
    def bridge_decl_names(self) -> List[str]:
        names = list(self.bridge_names or [])
        if not names:
            names = list(
                getattr(self.scope, "executable_bridge_decl_names", lambda: [])()
            )
        return list(
            dict.fromkeys(str(name).strip() for name in names if str(name).strip())
        )


@dataclass(frozen=True)
class RootContractHole:
    """One Lean-extracted hole from a checked root composition scaffold."""

    hole_id: str
    goal_statement: str
    local_argc: int = 0
    goal_target: str = ""
    hypotheses: List[str] = field(default_factory=list)
    binders: str = ""
    source_claim_statement: str = ""
    source_slot_id: str = ""
    source_helper_name: str = ""
    role: str = "root"

    @property
    def statement(self) -> str:
        return str(self.goal_statement or "")


@dataclass(frozen=True)
class CheckedDecompositionContract:
    """Lean-checked root composition contract derived from solved support."""

    contract_id: str = ""
    root_statement: str = ""
    support_fingerprint: str = ""
    scaffold_proof: str = ""
    holes: List[RootContractHole] = field(default_factory=list)
    solved_claim_statements: List[str] = field(default_factory=list)
    solved_claim_names: List[str] = field(default_factory=list)
    pending_claim_statements: List[str] = field(default_factory=list)
    pending_claim_slot_ids: List[str] = field(default_factory=list)
    pending_claim_helper_names: List[str] = field(default_factory=list)
    compile_ok: bool = False
    active: bool = False
    fallback_reason: str = ""
    compile_error_type: str = ""
    compile_diagnostic_preview: str = ""
    compile_returncode: int = 0

    @property
    def unsolved_claim_statements(self) -> List[str]:
        return list(self.pending_claim_statements)

    @property
    def compiled(self) -> bool:
        return bool(self.compile_ok)

    @classmethod
    def refresh_from(cls, workset: Any) -> "CheckedDecompositionContract":
        """Rebuild the checked-contract view from the canonical RootWorkset."""
        nodes = _workset_nodes(workset)
        root_statement = _workset_root_statement(workset, nodes)
        support_nodes = _workset_support_nodes(workset, nodes)
        hole_nodes = [
            node
            for node in nodes
            if _workset_enum_value(getattr(node, "kind", "")) in _WORKSET_SLOT_KINDS
            and _workset_enum_value(getattr(node, "status", ""))
            not in (*_WORKSET_SOLVED_STATUSES, "rejected")
            and _workset_node_statement(node)
        ]
        holes: List[RootContractHole] = []
        for idx, node in enumerate(hole_nodes, start=1):
            metadata = _workset_metadata(node)
            name = str(getattr(node, "name", "") or "").strip() or f"hole_{idx}"
            statement = _workset_node_statement(node)
            holes.append(
                RootContractHole(
                    hole_id=str(metadata.get("hole_id", "") or name),
                    goal_statement=statement,
                    local_argc=_workset_int(metadata.get("local_argc", 0), 0),
                    goal_target=str(metadata.get("goal_target", "") or statement),
                    hypotheses=_workset_str_list(metadata.get("hypotheses", [])),
                    binders=str(metadata.get("binders", "") or ""),
                    source_claim_statement=str(
                        metadata.get("source_claim_statement", "") or statement
                    ),
                    source_slot_id=str(metadata.get("source_slot_id", "") or name),
                    source_helper_name=str(metadata.get("source_helper_name", "") or ""),
                    role=str(metadata.get("role", "") or "root"),
                )
            )

        solved_names = _workset_support_names(workset, nodes)
        solved_statement_by_name = {
            str(getattr(node, "name", "") or "").strip(): _workset_node_statement(node)
            for node in support_nodes
        }
        pending_slot_ids = [hole.hole_id for hole in holes]
        fingerprint = _workset_fingerprint(
            root_statement,
            solved_names,
            [hole.goal_statement for hole in holes],
        )
        root_metadata = {}
        for node in nodes:
            if _workset_enum_value(getattr(node, "kind", "")) == "root_claim":
                root_metadata = _workset_metadata(node)
                break
        return cls(
            contract_id=str(root_metadata.get("contract_id", "") or f"workset:{fingerprint}"),
            root_statement=root_statement,
            support_fingerprint=fingerprint,
            scaffold_proof=str(root_metadata.get("scaffold_proof", "") or ""),
            holes=holes,
            solved_claim_statements=[
                solved_statement_by_name.get(name, "") for name in solved_names
            ],
            solved_claim_names=solved_names,
            pending_claim_statements=[hole.goal_statement for hole in holes],
            pending_claim_slot_ids=pending_slot_ids,
            pending_claim_helper_names=[
                hole.source_helper_name for hole in holes if hole.source_helper_name
            ],
            compile_ok=bool(root_metadata.get("compile_ok", False) or not holes),
            active=bool(root_statement or solved_names or holes),
            fallback_reason=str(root_metadata.get("fallback_reason", "") or ""),
            compile_error_type=str(root_metadata.get("compile_error_type", "") or ""),
            compile_diagnostic_preview=str(
                root_metadata.get("compile_diagnostic_preview", "") or ""
            ),
            compile_returncode=_workset_int(
                root_metadata.get("compile_returncode", 0), 0
            ),
        )


@dataclass
class RootIntegrationState:
    """Mutable root-integration controller state for one search session."""

    phase: RootIntegrationPhase = RootIntegrationPhase.EXPLORE
    focus_rounds_remaining: int = 0
    legacy_concentrated_lock: bool = False
    active_support_controller_key: str = ""
    active_support_fingerprint: str = ""
    last_support_fingerprint: str = ""
    failure_counts_by_support: Dict[str, int] = field(default_factory=dict)
    exhausted_support_controller_keys: set[str] = field(default_factory=set)
    exhausted_support_fingerprints: set[str] = field(default_factory=set)
    # Phase 5 Blocker 2 — granular per-support exhaustion counter.
    # The binary set above tells the legacy retrigger "is this support
    # currently cooled off?"; the count tells the three-lane arbiter
    # "how many times has this support already been focus-scheduled?"
    # so it can decay, reshuffle, or hand the work to a different lane
    # under a tighter budget profile. Kept in sync with the set — when
    # the set is cleared on success, this dict entry also clears.
    exhausted_support_attempts: Dict[str, int] = field(default_factory=dict)
    current_support: Optional[RootSupportSnapshot] = None
    support_audits: Dict[str, RootSupportAudit] = field(default_factory=dict)
    last_support_audit: Optional[RootSupportAudit] = None
    support_audit_calls: int = 0
    audit_obligation_fingerprints_seen: set[str] = field(default_factory=set)


@dataclass
class SearchSession:
    """Explicit mutable state for run_tree_search().

    Replaces implicit closure capture and nonlocal variables with a single
    dataclass that is threaded through all closures.  Every field that was
    previously a ``nonlocal`` or a captured mutable in ``run_tree_search()``
    is declared here, making the state surface auditable and testable.
    """

    # ── Identity ──────────────────────────────────────────────────────
    statement: str = ""
    # Explicit-binder view of ``statement`` for LLM prompt consumption.
    # Lean 4's implicit/instance/strict-implicit binders (``{x:T}`` /
    # ``[x:T]`` / ``⦃x:T⦄``) are auto-bound by the elaborator; the LLM,
    # reading raw text, counts them as explicit and over-extends
    # ``intro`` chains. ``make_forall_binders_explicit`` (utils.py:3067)
    # rewrites them to ``(x:T)``. See worklogs/2026-04-24_intro_binder_rewrite_fix.log.
    # Kept SEPARATE from ``statement`` because the rewrite mutates the
    # theorem type in Lean 4 — only prompt surfaces use this form;
    # verification, cache keys, proven-lemma index, and lemma lookup
    # continue to use ``statement`` unchanged.
    statement_explicit: str = ""
    depth: int = 0
    mode: str = "beam"

    # ── Timing ────────────────────────────────────────────────────────
    tree_search_t0: float = 0.0
    tree_search_exempt_t0: float = 0.0

    # ── Node tracking (nonlocal in prove_fn) ──────────────────────────
    nodes_evaluated: int = 0

    # ── Policy (nonlocal in prove_fn) ─────────────────────────────────
    active_policy: Optional[MasterPolicy] = None
    root_time_budget_s: Optional[float] = None
    root_form_reserve_s: Optional[float] = None

    # ── Replan state (nonlocal in prove_fn) ───────────────────────────
    replan_signal_fired: bool = False
    # Scaffold-owned replan signal. This is separate from the refiner's
    # REPLAN_REQUESTED path because Lean refuting a compiled scaffold slot is
    # structural evidence about the decomposition itself, and must still
    # interrupt search when cfg.search.refiner_can_replan is disabled.
    scaffold_refutation_replan_fired: bool = False
    scaffold_refutation_replan_fingerprint: str = ""
    # Refiner-originated REPLAN_REQUESTED emitted while executing a compiled
    # scaffold slot. Separate from Lean refutation because this is an advisory
    # decomposition signal, but it still needs to interrupt scaffold retries.
    scaffold_slot_replan_fired: bool = False
    scaffold_slot_replan_fingerprint: str = ""
    scaffold_slot_replan_payload: str = ""
    replan_ctx: Optional[ReplanContext] = None
    refiner_suggestions: List[str] = field(default_factory=list)
    refiner_hints: List[DirectedHint] = field(default_factory=list)
    refiner_hints_by_stmt: Dict[str, List[DirectedHint]] = field(default_factory=dict)

    # ── Proven-lemma retrieval cache (nonlocal in expand_fn) ──────────
    guard_proven_lemmas: Optional[list] = None
    guard_proven_lemma_retrieval_attempts: int = 0
    guard_proven_lemma_retrieval_max_attempts: int = 3
    # Per-statement proven-lemma cache: avoids root→subgoal contamination.
    # Keyed by whitespace-normalized statement text.
    guard_proven_lemma_cache: Dict[str, list] = field(default_factory=dict)
    guard_blocked_proven_names_by_stmt: Dict[str, List[str]] = field(
        default_factory=dict
    )
    guard_proven_lemma_stmt_retries: Dict[str, int] = field(default_factory=dict)

    # ── Session-level failed proof hashes (synth-ref gated) ────────────
    # Legacy aggregate set retained for backward-compatible state shape.
    # New logic uses the goal-fingerprint keyed map below.
    session_failed_synth_proof_hashes: set = field(default_factory=set)
    # Failed synth-ref proof hashes scoped by goal fingerprint so one
    # subgoal's failure does not globally blacklist the same proof text.
    session_failed_synth_proof_hashes_by_goal: Dict[str, set] = field(
        default_factory=dict
    )

    # ── Failure tracking (captured mutable in closures) ───────────────
    node_error_log: Dict[str, Tuple[str, str, float]] = field(default_factory=dict)
    stmt_failure_summaries: Dict[str, List[FailureRoundSummary]] = field(
        default_factory=dict
    )
    # Refiner pattern feedback: patterns extracted from refiner successes
    refiner_patterns: List[RefinerPattern] = field(default_factory=list)
    stmt_failed_proof_hashes: Dict[str, List[str]] = field(default_factory=dict)
    stmt_failed_error_by_hash: Dict[str, Dict[str, str]] = field(default_factory=dict)
    stmt_failed_error_type_by_hash: Dict[str, Dict[str, str]] = field(
        default_factory=dict
    )
    stmt_failed_goal_contract_signatures: Dict[str, List[str]] = field(
        default_factory=dict
    )
    stmt_failed_goal_contract_counts: Dict[str, Dict[str, int]] = field(
        default_factory=dict
    )

    # ── Per-statement stagnation (persists across beam restarts) ─────
    # Tracks consecutive no-progress attempts per normalized statement
    # across restarts. When a statement crosses the threshold, prove_fn
    # short-circuits to prevent 500-attempt stagnation loops.
    stmt_consecutive_failures: Dict[str, int] = field(default_factory=dict)
    stmt_stagnation_skips: int = 0

    # ── Restart loop state ────────────────────────────────────────────
    restart_count: int = 0
    cumulative_nodes: int = 0
    cumulative_max_depth: int = 0
    cumulative_solved_non_root_keys: Dict[str, None] = field(default_factory=dict)
    root_solved: bool = False
    early_falsified: bool = False
    root_search_attempted: bool = False
    depth0_starvation_rounds: int = 0
    per_restart_log: List[Dict[str, Any]] = field(default_factory=list)

    # ── Evidence-gated restart snapshots (WI-4) ───────────────────────
    # Captured at each restart decision point so the next restart can
    # compare against them.  Prevents restarting when no net-new
    # progress was made (same solved count, same depth, no new subgoals).
    last_restart_solved_count: int = 0
    last_restart_non_root_solved_count: int = 0
    last_restart_max_depth: int = 0
    last_restart_subgoal_count: int = 0
    last_restart_audit_queue_goal_ids: set[str] = field(default_factory=set)

    # ── Composition / root-focused mode ───────────────────────────────
    composition_failures: int = (
        0  # checked stitch failures (Lean or proof policy rejected)
    )
    # Event-driven composition retrigger: set by
    # Orchestrator._maybe_request_composition_retrigger when a non-root
    # helper is registered while root search is active. The beam's
    # should_continue callback converts this into an early exit so the
    # tree_search loop head can re-evaluate composition with the fresh
    # support snapshot. Cleared via _consume_composition_retrigger.
    composition_retrigger_pending: bool = False
    composition_last_attempt_support_fp: str = ""
    # Legacy compatibility flag. The root controller is authoritative; this
    # mirrors whether a root-focus round is currently active.
    root_concentrated: bool = False
    root_integration: RootIntegrationState = field(default_factory=RootIntegrationState)
    active_root_contract: Optional[CheckedDecompositionContract] = None
    active_theorem_scaffold: Optional[TheoremScaffold] = None
    active_compiled_scaffold: Optional[CompiledScaffoldState] = None
    blocked_compiled_scaffold_ids: Dict[str, str] = field(default_factory=dict)

    # ── Refuted-witness ledger (Phase 2 of decide-refutation feedback) ─
    # Records (statement_hash, witness_hash) -> entry for every witness that
    # Lean has refuted within the current problem. Surfaced to the planner
    # at replan time via ReplanContext.refuted_witnesses so the LLM can
    # re-derive a different witness instead of re-emitting refuted ones.
    #
    # Honesty contract: this is a transcript of Lean verdicts, NOT a system
    # filter. The ledger is read-only context for the planner prompt. The
    # system MUST NEVER:
    #   - Reject planner output containing a refuted witness (Lean re-checks)
    #   - Pre-filter candidates against the ledger before sending to Lean
    #   - Augment the ledger with system-generated suggestions
    #
    # Schema (key = f"{statement_hash}:{witness_hash}"):
    #   {
    #     "statement_hash": str,
    #     "witness_hash":   str,
    #     "witness_text":   str,    # normalized witness expression
    #     "shape":          str,    # GoalShape enum value
    #     "evidence":       str,    # ≤256 chars of Lean output
    #     "first_seen_at":  float,
    #     "last_seen_at":   float,
    #     "count":          int,
    #     "slot_id":        str,
    #     "scaffold_id":    str,
    #   }
    #
    # Per-problem scope: SearchSession is local to run_tree_search() so
    # the ledger auto-resets at problem boundary.
    refuted_witness_ledger: Dict[str, Dict[str, Any]] = field(default_factory=dict)

    # ── Proof potential (observe/prune) ───────────────────────────────
    proof_potential_trace: List[Dict[str, Any]] = field(default_factory=list)
    proof_potential_last_by_stmt: Dict[str, float] = field(default_factory=dict)
    proof_potential_nondec_streak: Dict[str, int] = field(default_factory=dict)
    proof_potential_samples: int = 0
    proof_potential_sum: float = 0.0
    proof_potential_best: float = float("inf")
    proof_potential_escape_used: int = 0
    proof_potential_pruned: int = 0

    @property
    def root_focus_active(self) -> bool:
        return bool(self.root_concentrated)
