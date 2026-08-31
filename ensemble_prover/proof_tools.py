"""Tool-augmented proving: LLM-callable tools for mid-proof Mathlib search and type inspection."""

from __future__ import annotations

import json
import logging
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any, Dict, List, Mapping, Optional

from .mathlib_api_search import MathlibApiSearcher
from .utils import (
    is_non_theorem_standalone_lean_expr,
    looks_like_lean_type,
    parse_tool_arguments,
)

if TYPE_CHECKING:
    from .lean_runner import LeanRunner
    from .lemma_retriever import LemmaRetriever

logger = logging.getLogger(__name__)
_LEAN_DECL_NAME_RE = re.compile(r"^[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*$")
_SYNTHETIC_STRING_PLACEHOLDER_RE = re.compile(
    r'(?<![A-Za-z0-9_])(?:"<string>"|<string>)(?![A-Za-z0-9_])',
    re.IGNORECASE,
)


def normalize_theorem_search_query(query: Any) -> tuple[str, int]:
    """Remove Mini prompt-redaction sentinels before theorem retrieval."""

    raw = str(query or "").strip()
    if not raw:
        return "", 0
    cleaned, removed = _SYNTHETIC_STRING_PLACEHOLDER_RE.subn(" ", raw)
    cleaned = " ".join(cleaned.split()).strip(" \t\r\n\"'")
    return cleaned, int(removed)


def _decode_tool_arguments(arguments: str) -> tuple[Optional[Dict[str, Any]], str]:
    """Decode JSON tool arguments into a mapping or return an error string."""
    decoded, error = parse_tool_arguments(arguments)
    if error:
        return None, f"Error: malformed arguments JSON: {error}"
    if not isinstance(decoded, Mapping):
        return None, "Error: tool arguments must decode to a JSON object."
    return dict(decoded), ""


# ---------------------------------------------------------------------------
# Tool schemas (OpenAI function-calling format)
# ---------------------------------------------------------------------------

SEARCH_MATHLIB_TOOL: Dict[str, Any] = {
    "type": "function",
    "function": {
        "name": "search_mathlib",
        "description": (
            "Search the static Mathlib API for theorems, lemmas, and definitions. "
            "Returns name and full type signature for each match. "
            "Use a Lean name fragment (e.g. 'integral_comp_sub'), "
            "a type pattern (e.g. '∫ f ∘ g'), or a natural language "
            "description (e.g. 'change of variables for interval integral'). "
            "Never use prompt-redaction tokens such as '<string>' as terms. "
            "This tool does not search local theorem declarations or generated support lemmas; "
            "use `check_type` for those."
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "query": {
                    "type": "string",
                    "description": "Search query",
                },
                "kind": {
                    "type": "string",
                    "enum": ["any", "theorem", "lemma", "def"],
                    "description": "Filter by declaration kind",
                },
            },
            "required": ["query"],
        },
    },
}

CHECK_TYPE_TOOL: Dict[str, Any] = {
    "type": "function",
    "function": {
        "name": "check_type",
        "description": (
            "Run Lean 4 #check on a declaration name and return its exact type signature. "
            "Use this to verify a lemma's real argument names and types "
            "before using it in a proof. Only bare Lean declaration names "
            "or namespace-qualified constant names are supported."
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "term": {
                    "type": "string",
                    "description": "A Lean declaration name (e.g. 'intervalIntegral.integral_comp_sub_left')",
                },
            },
            "required": ["term"],
        },
    },
}

def _apply_decl_to_goal_tool(*, active_goal_bound: bool) -> Dict[str, Any]:
    if active_goal_bound:
        description = (
            "Ask Lean whether a theorem or lemma can be applied to the active goal "
            "provided by the harness. Only use declaration names from search_mathlib "
            "results or previous type-checking output — "
            "do not call this with problem-local definitions, constants, or solution values "
            "(they are not theorems and will always fail). "
            "It tries exact/apply/refine proof-stub shapes and returns structured JSON "
            "with an accepted proof stub and the remaining subgoals when it fits."
        )
        statement_description = (
            "Optional legacy field. In mini_prover/mini_session this is ignored "
            "because the harness supplies the active goal."
        )
        required = ["decl_name"]
    else:
        description = (
            "Ask Lean whether a theorem or lemma can be applied to an explicit goal "
            "statement. Only use declaration names from search_mathlib results or "
            "previous type-checking output — do not call this with problem-local "
            "definitions, constants, or solution values (they are not theorems and "
            "will always fail). It tries exact/apply/refine proof-stub shapes and "
            "returns structured JSON with an accepted proof stub and the remaining "
            "subgoals when it fits."
        )
        statement_description = "The exact theorem statement or goal being proved."
        required = ["statement", "decl_name"]
    return {
        "type": "function",
        "function": {
            "name": "apply_decl_to_goal",
            "description": description,
            "parameters": {
                "type": "object",
                "properties": {
                    "statement": {
                        "type": "string",
                        "description": statement_description,
                    },
                    "decl_name": {
                        "type": "string",
                        "description": (
                            "A Lean theorem or lemma name to probe against the goal. "
                            "Use names from search_mathlib or type-checking results."
                        ),
                    },
                },
                "required": required,
            },
        },
    }


APPLY_DECL_TO_GOAL_TOOL: Dict[str, Any] = _apply_decl_to_goal_tool(
    active_goal_bound=False
)
APPLY_DECL_TO_ACTIVE_GOAL_TOOL: Dict[str, Any] = _apply_decl_to_goal_tool(
    active_goal_bound=True
)

PROOF_TOOLS: List[Dict[str, Any]] = [
    SEARCH_MATHLIB_TOOL,
    CHECK_TYPE_TOOL,
    APPLY_DECL_TO_GOAL_TOOL,
]


# ---------------------------------------------------------------------------
# ProofToolkit — executes tool calls against static API search, support retrieval, and Lean
# ---------------------------------------------------------------------------


@dataclass
class ProofToolkit:
    """Wraps static API search, support retrieval, and LeanRunner to service tool calls."""

    retriever: Optional[LemmaRetriever]
    lean: LeanRunner
    preamble_override: Optional[str] = None
    context_lemmas: List[str] = field(default_factory=list)
    current_problem_path: Optional[str] = None
    current_theorem_name: Optional[str] = None
    max_search_results: int = 10
    check_type_timeout_s: float = 10.0
    api_searcher: Optional[MathlibApiSearcher] = None
    _current_problem_decl_cache: Optional[tuple[str, int, List[Any]]] = field(
        default=None, init=False, repr=False
    )

    @staticmethod
    def _format_entry(entry: Any) -> str:
        return f"{entry.name} : {entry.type}"

    @property
    def support_retriever(self) -> Optional[LemmaRetriever]:
        """Backward-compatible view of the dynamic support retriever."""
        return self.retriever

    def _load_local_decl_entries(self) -> List[Any]:
        if not self.support_retriever:
            return []
        extractor = getattr(self.support_retriever, "_extract_local_decls", None)
        if not callable(extractor):
            return []
        try:
            return list(extractor(self.preamble_override or ""))
        except Exception as exc:
            logger.debug("local declaration extraction failed: %s", exc, exc_info=True)
            return []

    def _load_current_problem_decl_entries(self) -> List[Any]:
        problem_path = str(self.current_problem_path or "").strip()
        if not problem_path:
            return []
        file_path = Path(problem_path)
        if not file_path.exists():
            return []
        try:
            stat_result = file_path.stat()
            mtime_ns = int(getattr(stat_result, "st_mtime_ns", 0) or 0)
        except OSError:
            mtime_ns = 0
        cached = self._current_problem_decl_cache
        if cached and cached[0] == str(file_path) and cached[1] == mtime_ns:
            return self._scope_current_problem_decl_entries(cached[2])
        try:
            text = file_path.read_text(encoding="utf-8")
            from .lemma_retriever import _scan_file

            entries = list(_scan_file(text, file_path))
        except Exception as exc:
            logger.debug(
                "current problem declaration scan failed for %s: %s",
                file_path,
                exc,
                exc_info=True,
            )
            entries = []
        self._current_problem_decl_cache = (str(file_path), mtime_ns, list(entries))
        return self._scope_current_problem_decl_entries(entries)

    def _scope_current_problem_decl_entries(self, entries: List[Any]) -> List[Any]:
        theorem_name = str(self.current_theorem_name or "").strip()
        if not theorem_name:
            return list(entries)
        scoped: List[Any] = []
        for entry in entries:
            scoped.append(entry)
            entry_name = str(getattr(entry, "name", "") or "").strip()
            if entry_name == theorem_name:
                return scoped
        return list(entries)

    def _find_exact_api_decl_matches(self, name: str, *, kind: str = "any") -> List[Any]:
        target = str(name or "").strip()
        searcher = self._mathlib_api_searcher()
        if not target or searcher is None:
            return []
        try:
            hits = searcher.search_with_scores(
                target,
                kind=kind,
                max_results=max(8, int(self.max_search_results)),
            )
        except Exception as exc:
            logger.debug("exact api lookup failed for %s: %s", target, exc, exc_info=True)
            return []
        matches: List[Any] = []
        seen: set[str] = set()
        for hit in hits:
            entry = getattr(hit, "entry", None)
            entry_name = str(getattr(entry, "name", "") or "").strip()
            if entry is None or entry_name != target or entry_name in seen:
                continue
            seen.add(entry_name)
            matches.append(entry)
        return matches

    def _find_exact_authoritative_decl_matches(
        self, name: str, *, kind: str = "any"
    ) -> List[Any]:
        target = str(name or "").strip()
        if not target:
            return []
        matches: List[Any] = []
        seen: set[str] = set()

        def _append(entries: List[Any]) -> None:
            for entry in entries:
                entry_name = str(getattr(entry, "name", "") or "").strip()
                entry_kind = str(getattr(entry, "kind", "") or "").strip()
                if entry_name != target:
                    continue
                if kind != "any" and entry_kind != kind:
                    continue
                if entry_name in seen:
                    continue
                seen.add(entry_name)
                matches.append(entry)

        # Only declarations that are authoritative for the active Lean scope may
        # short-circuit a Lean query here. Project/support index entries are
        # retrieval hints, not proof-tool resolution authority.
        _append(self._load_current_problem_decl_entries())
        _append(self._load_local_decl_entries())
        _append(self._find_exact_api_decl_matches(target, kind=kind))
        return matches

    @staticmethod
    def _decl_entry_kind(entry: Any) -> str:
        return str(getattr(entry, "kind", "") or "").strip().lower()

    @classmethod
    def _decl_entry_is_goal_applicable(cls, entry: Any) -> bool:
        kind = cls._decl_entry_kind(entry)
        if kind in {"theorem", "lemma", "axiom"}:
            return True
        type_text = str(getattr(entry, "type", "") or "").strip()
        if not type_text or not looks_like_lean_type(type_text):
            return False
        return not is_non_theorem_standalone_lean_expr(type_text)

    def _find_exact_current_problem_decl(self, name: str) -> Optional[Any]:
        target = str(name or "").strip()
        if not target:
            return None
        for entry in self._load_current_problem_decl_entries():
            if str(getattr(entry, "name", "") or "").strip() == target:
                return entry
        return None

    def _find_exact_local_decl(self, name: str) -> Optional[Any]:
        target = str(name or "").strip()
        if not target:
            return None
        for entry in self._load_local_decl_entries():
            if str(getattr(entry, "name", "") or "").strip() == target:
                return entry
        return None

    @staticmethod
    def _extract_decl_name_from_context_lemma(text: str) -> str:
        raw = str(text or "").strip()
        if not raw:
            return ""
        decl_match = re.match(
            r"^(?:private\s+)?(?:theorem|lemma|def|abbrev|axiom)\s+"
            r"([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)\b",
            raw,
        )
        if decl_match:
            return str(decl_match.group(1) or "").strip()
        head = raw.split(":=", 1)[0].strip()
        if ":" in head:
            head = head.split(":", 1)[0].strip()
        if not head:
            return ""
        candidate = head.split()[-1].strip()
        return candidate if _LEAN_DECL_NAME_RE.match(candidate) else ""

    def _known_local_decl_names(self) -> set[str]:
        names: set[str] = set()
        for entry in self._load_local_decl_entries():
            name = str(getattr(entry, "name", "") or "").strip()
            if name:
                names.add(name)
        for lemma_text in list(self.context_lemmas or []):
            name = self._extract_decl_name_from_context_lemma(str(lemma_text or ""))
            if name:
                names.add(name)
        return names

    def _is_known_local_decl_name(self, name: str) -> bool:
        target = str(name or "").strip()
        return bool(target and target in self._known_local_decl_names())

    def _is_self_reference_decl(self, name: str) -> bool:
        theorem_name = str(self.current_theorem_name or "").strip()
        target = str(name or "").strip()
        return bool(theorem_name and target and target == theorem_name)

    def _mathlib_api_searcher(self) -> Optional[MathlibApiSearcher]:
        return self.api_searcher

    async def execute(self, name: str, arguments: str) -> str:
        """Dispatch a tool call by name. *arguments* is a JSON string."""
        args, error = _decode_tool_arguments(arguments)
        if args is None:
            return error
        if name == "search_mathlib":
            return await self.search_mathlib(**args)
        if name == "check_type":
            return await self.check_type(**args)
        if name == "apply_decl_to_goal":
            return await self.apply_decl_to_goal(**args)
        return f"Error: unknown tool '{name}'"

    async def search_mathlib(
        self, query: str = "", kind: str = "any", **_kw: Any
    ) -> str:
        """Search the static Mathlib API and return formatted results."""
        query, removed_placeholders = normalize_theorem_search_query(query)
        if not query:
            if removed_placeholders:
                return (
                    "Error: query contained only synthetic <string> redaction "
                    "placeholders; search was not dispatched. Supply concrete "
                    "Mathlib names or mathematical terms."
                )
            return "Error: empty query"
        searcher = self._mathlib_api_searcher()
        if not searcher:
            return "Error: Mathlib retrieval is not enabled in this configuration."
        if (
            self._is_self_reference_decl(query)
            or self._is_known_local_decl_name(query)
            or self._find_exact_current_problem_decl(query) is not None
        ):
            return (
                "No matching Mathlib declarations found. "
                "Use check_type for local or current-theorem declarations."
            )
        try:
            hits = searcher.search_with_scores(
                query,
                kind=kind,
                max_results=self.max_search_results,
            )
        except Exception as exc:
            logger.debug("search_mathlib raised: %s", exc, exc_info=True)
            return f"Error: retrieval failed: {exc}"
        exact_query = _LEAN_DECL_NAME_RE.match(query) is not None
        exact_matches = (
            self._find_exact_api_decl_matches(query, kind=kind)
            if exact_query
            else []
        )
        results: List[str] = []
        seen_names: set[str] = set()
        for entry in exact_matches:
            entry_name = str(getattr(entry, "name", "") or "").strip()
            if not entry_name or self._is_self_reference_decl(entry_name):
                continue
            seen_names.add(entry_name)
            results.append(f"{entry.name} : {entry.type}")
        for hit in hits:
            entry = hit.entry
            entry_name = str(getattr(entry, "name", "") or "").strip()
            if (
                not entry_name
                or entry_name in seen_names
                or self._is_self_reference_decl(entry_name)
            ):
                continue
            seen_names.add(entry_name)
            results.append(f"{entry.name} : {entry.type}")
        if not results:
            if exact_query:
                rendered = "exact_match=false\nNo matching lemmas found."
            else:
                rendered = "No matching lemmas found."
            if removed_placeholders:
                return (
                    f"Ignored {removed_placeholders} synthetic <string> "
                    f"placeholder(s); effective query: {query}\n{rendered}"
                )
            return rendered
        if exact_query:
            prefix = "exact_match=true" if exact_matches else "exact_match=false"
            if not exact_matches:
                prefix += "\nFuzzy matches only; verify names with check_type before use."
            rendered = "\n".join([prefix, *results[: self.max_search_results]])
        else:
            rendered = "\n".join(results[: self.max_search_results])
        if removed_placeholders:
            rendered = (
                f"Ignored {removed_placeholders} synthetic <string> "
                f"placeholder(s); effective query: {query}\n{rendered}"
            )
        return rendered

    async def check_type(self, term: str = "", **_kw: Any) -> str:
        """Run ``#check <term>`` via the Lean runner.

        Structural fix (2026-04-16): the prior early-rejection branch
        rejected any unqualified name (no ``.``) that wasn't in the local
        decl cache, even when Lean would resolve it correctly via the
        ``import Mathlib`` preamble (e.g. ``mul_comm``, ``mul_assoc``,
        ``congrArg``).  That asymmetry made the tool loop diverge — the
        sibling ``search_mathlib`` would find the lemma but ``check_type``
        would falsely reject it, leading to "repeated call detected,
        forcing finalize" failures (see putnam_2012_a2 trace).  Lean is
        now the sole authority for resolution; the static-index hits are
        still preferred when present (cheaper, no Lean call), but absence
        from the index no longer blocks Lean from being consulted.
        """
        term = str(term or "").strip()
        if not term:
            return "Error: empty term"
        if self._is_self_reference_decl(term):
            return (
                "Error: self-referential declaration is blocked during proving: "
                f"{term}"
            )
        exact_local_decl = self._find_exact_local_decl(term)
        exact_current_decl = self._find_exact_current_problem_decl(term)
        exact_api_matches = self._find_exact_api_decl_matches(term)
        known_local_decl = (
            self._is_known_local_decl_name(term) or exact_local_decl is not None
        )
        # Lean is authoritative — always try resolution rather than
        # bypassing it for unqualified names.  Static Mathlib index
        # signatures omit implicit typeclass binders for declarations such
        # as `mul_assoc`; returning those as checked types misled prover
        # prompts into using associativity in a bare `[Mul S]` context.
        try:
            result = await self.lean.check_term_type(
                term,
                preamble_override=self.preamble_override,
                lemmas=list(self.context_lemmas or []),
                timeout_s=self.check_type_timeout_s,
            )
        except Exception as exc:
            logger.debug("check_type raised: %s", exc, exc_info=True)
            result = f"Error: #check failed: {exc}"
        if not str(result).startswith("Error:"):
            return result
        if exact_local_decl is not None:
            return self._format_entry(exact_local_decl)
        if exact_current_decl is not None:
            return self._format_entry(exact_current_decl)
        if exact_api_matches and not known_local_decl:
            return (
                "Static index fallback (Lean #check failed; implicit "
                "typeclass binders may be omitted): "
                + self._format_entry(exact_api_matches[0])
            )
        return result

    async def apply_decl_to_goal(
        self,
        statement: str = "",
        decl_name: str = "",
        **_kw: Any,
    ) -> str:
        """Return a structured applicability probe for one declaration."""
        statement = str(statement or "").strip()
        decl_name = str(decl_name or "").strip()
        if not statement:
            return json.dumps(
                {
                    "decl_name": decl_name,
                    "statement": statement,
                    "applicable": False,
                    "proof_stub": "",
                    "remaining_goals": [],
                    "instantiated_target": statement,
                    "error_kind": "empty_statement",
                },
                ensure_ascii=False,
                sort_keys=True,
            )
        if not decl_name:
            return json.dumps(
                {
                    "decl_name": decl_name,
                    "statement": statement,
                    "applicable": False,
                    "proof_stub": "",
                    "remaining_goals": [],
                    "instantiated_target": statement,
                    "error_kind": "empty_decl_name",
                },
                ensure_ascii=False,
                sort_keys=True,
            )
        if self._is_self_reference_decl(decl_name):
            return json.dumps(
                {
                    "decl_name": decl_name,
                    "statement": statement,
                    "applicable": False,
                    "proof_stub": "",
                    "remaining_goals": [],
                    "instantiated_target": statement,
                    "error_kind": "self_reference_decl",
                },
                ensure_ascii=False,
                sort_keys=True,
            )
        exact_matches = self._find_exact_authoritative_decl_matches(decl_name)
        if exact_matches:
            if not any(self._decl_entry_is_goal_applicable(entry) for entry in exact_matches):
                return json.dumps(
                    {
                        "decl_name": decl_name,
                        "statement": statement,
                        "applicable": False,
                        "proof_stub": "",
                        "remaining_goals": [],
                        "instantiated_target": statement,
                        "error_kind": "non_theorem_decl",
                    },
                    ensure_ascii=False,
                    sort_keys=True,
                )
        # Note: an earlier short-circuit here returned ``unknown_decl_name``
        # for any unqualified identifier not already in the local /
        # support-retriever index, WITHOUT consulting Lean. That created
        # an asymmetry with ``check_type`` (which DOES ask Lean for
        # unqualified names via Real.Mathlib resolution). Live evidence
        # from 2009_b2_18apr_10.jsonl and 1983_a1_18apr_3.jsonl: the LLM
        # first ran ``check_type("sub_nonneg")`` — Lean resolved it
        # successfully — then the orchestrator auto-called
        # ``apply_decl_to_goal("sub_nonneg", ...)`` which pre-rejected
        # with ``unknown_decl_name`` because ``sub_nonneg`` was not in any
        # static index. The Apr-16 blocker then banned the (real) decl
        # for the rest of the run. Removing the short-circuit lets Lean
        # be the authority for unqualified names; truly-fake names come
        # back from Lean as ``unknown_identifier`` (not
        # ``unknown_decl_name``) and the blocker's decisive set does
        # NOT include ``unknown_identifier`` so no false bans.
        try:
            result = await self.lean.apply_decl_to_goal(
                statement,
                decl_name,
                preamble_override=self.preamble_override,
                lemmas=list(self.context_lemmas or []),
                timeout_s=self.check_type_timeout_s,
            )
        except Exception as exc:
            logger.debug("apply_decl_to_goal raised: %s", exc, exc_info=True)
            result = {
                "decl_name": decl_name,
                "statement": statement,
                "applicable": False,
                "proof_stub": f"refine {decl_name} ?_",
                "remaining_goals": [],
                "instantiated_target": statement,
                "error_kind": "runner_exception",
                "error": str(exc),
            }
        return json.dumps(result, ensure_ascii=False, sort_keys=True)
