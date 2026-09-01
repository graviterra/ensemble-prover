"""Shared hashing, text, Lean-source, and proof-candidate utilities."""

from __future__ import annotations

import hashlib
import json
import math
import re
import threading
import time
import unicodedata
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Set


def now_ts() -> float:
    return time.time()


def format_exception(exc: BaseException) -> str:
    """Render exceptions robustly (some, like httpx.ReadTimeout(''), stringify to '')."""
    # Special-case HTTP status errors: include response body snippet (often contains
    # the real reason like "invalid_api_key" / "insufficient_quota").
    try:
        import httpx  # type: ignore

        if isinstance(exc, httpx.HTTPStatusError):
            body = ""
            try:
                body = (exc.response.text or "").strip()
            except Exception:
                body = ""
            if body:
                # Preserve the provider's error message OUTSIDE quoted JSON:
                # downstream prompt-safety redacts every double-quoted string
                # literal (a provider's 400 response once became an
                # undiagnosable `body={ "<string>": ... }` skeleton). Bare
                # text with quotes stripped survives that redaction, so the
                # actionable reason stays in run.log/turns.jsonl.
                provider_error = ""
                try:
                    error_obj = json.loads(body).get("error") or {}
                    message = " ".join(
                        str(error_obj.get("message") or "").split()
                    ).replace('"', "'")[:300]
                    if message:
                        error_type = (
                            str(error_obj.get("type") or "").strip() or "unknown"
                        )
                        error_code = (
                            str(error_obj.get("code") or "").strip() or "unknown"
                        )
                        provider_error = (
                            f" provider_error={error_type}/{error_code}: {message}"
                        )
                except Exception:
                    provider_error = ""
                if len(body) > 500:
                    body = body[:500] + "...(truncated)"
                return f"{type(exc).__name__}: {exc}{provider_error} body={body}"
    except Exception:
        pass
    try:
        msg = str(exc)
    except Exception:
        msg = ""
    if msg:
        return f"{type(exc).__name__}: {msg}"
    return f"{type(exc).__name__}: {exc!r}"


def display_line_count(text: Any) -> int:
    """Count displayed lines in a trace/rendered tool result."""
    rendered = str(text or "")
    if not rendered:
        return 0
    return len(rendered.splitlines())


def _reject_nonstandard_json_constant(value: str) -> None:
    raise ValueError(f"non-standard JSON constant {value!r}")


def _nonfinite_json_number_path(value: Any, *, path: str = "$") -> str:
    if isinstance(value, float) and not math.isfinite(value):
        return path
    if isinstance(value, dict):
        for item in value.values():
            child_path = f"{path}.<key>"
            found = _nonfinite_json_number_path(item, path=child_path)
            if found:
                return found
    if isinstance(value, list):
        for idx, item in enumerate(value):
            found = _nonfinite_json_number_path(item, path=f"{path}[{idx}]")
            if found:
                return found
    return ""


def parse_tool_arguments(raw_args: Any) -> tuple[Dict[str, Any], str]:
    """Parse strict JSON-object tool arguments, preserving compact failures."""
    if raw_args is None:
        return {}, "missing JSON arguments"
    text = str(raw_args)
    if not text.strip():
        return {}, "empty JSON arguments"
    try:
        parsed = json.loads(
            text,
            parse_constant=_reject_nonstandard_json_constant,
        )
    except Exception as exc:
        return {}, f"{type(exc).__name__}: {exc}"
    if not isinstance(parsed, dict):
        return {}, f"expected JSON object, got {type(parsed).__name__}"
    if "__malformed_arguments__" in parsed:
        return {}, "reserved internal key __malformed_arguments__ is not executable"
    nonfinite_path = _nonfinite_json_number_path(parsed)
    if nonfinite_path:
        return {}, f"non-finite JSON number at {nonfinite_path}"
    return parsed, ""


_TOKENIZER_CACHE: Dict[str, Any] = {}


_NON_OPENAI_MODEL_HINTS = (
    "llama",
    "qwen",
    "mistral",
    "mixtral",
    "deepseek",
    "phi",
    "gemma",
    "falcon",
    "mpt",
    "gpt-oss",
)


def _approx_chars_per_token(model: Optional[str]) -> float:
    if not model:
        return 4.0
    name = model.lower()
    if any(k in name for k in _NON_OPENAI_MODEL_HINTS):
        # Be conservative for llama-family tokenizers (Lean/math is denser than English).
        return 3.2
    return 4.0


def estimate_tokens(
    text: str,
    model: Optional[str] = None,
    *,
    chars_per_token: Optional[float] = None,
) -> int:
    """Estimate token count using tiktoken if available, else a heuristic."""
    s = (text or "").strip()
    if not s:
        return 0
    if chars_per_token is not None and chars_per_token > 0:
        return max(1, int(round(len(s) / float(chars_per_token))))
    # Avoid OpenAI-specific tokenization for non-OpenAI model families.
    use_tiktoken = True
    if model:
        name = model.lower()
        if any(k in name for k in _NON_OPENAI_MODEL_HINTS):
            use_tiktoken = False
    if use_tiktoken:
        try:
            import tiktoken  # type: ignore

            key = model or "cl100k_base"
            enc = _TOKENIZER_CACHE.get(key)
            if enc is None:
                enc = (
                    tiktoken.encoding_for_model(model)
                    if model
                    else tiktoken.get_encoding("cl100k_base")
                )
                _TOKENIZER_CACHE[key] = enc
            return len(enc.encode(s))
        except Exception:
            pass
    return max(1, int(round(len(s) / _approx_chars_per_token(model))))


def hash_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def canonical_source_key(source_theorem: Any) -> str:
    """Legacy basename key for source theorem compatibility/dedupe."""
    src = str(source_theorem or "").strip()
    if not src:
        return ""
    src = src.replace("\\", "/")
    if "/" in src:
        src = src.rsplit("/", 1)[-1]
    if src.endswith(".lean"):
        src = src[:-5]
    src = re.sub(r"\s+", " ", src).strip()
    if not src:
        return ""
    return src.lower()


def normalized_source_identity(source_theorem: Any) -> str:
    """Normalize the full source label while preserving path/module structure."""
    src = str(source_theorem or "").strip()
    if not src:
        return ""
    src = src.replace("\\", "/")
    if src.endswith(".lean"):
        src = src[:-5]
    src = re.sub(r"\s+", " ", src).strip()
    if not src:
        return ""
    return src.lower()


def _is_path_like_source(source_theorem: Any) -> bool:
    src = str(source_theorem or "").strip().replace("\\", "/")
    return "/" in src or src.endswith(".lean")


def _is_module_like_source(source_theorem: Any) -> bool:
    src = str(source_theorem or "").strip()
    return "." in src and not _is_path_like_source(src)


def _is_bare_source_stem(source_theorem: Any) -> bool:
    src = str(source_theorem or "").strip()
    if not src:
        return False
    return not _is_path_like_source(src) and not _is_module_like_source(src)


def source_theorem_matches(lhs: Any, rhs: Any) -> bool:
    """Return True when two source theorem labels refer to the same problem."""
    lhs_identity = normalized_source_identity(lhs)
    if not lhs_identity:
        return False
    rhs_identity = normalized_source_identity(rhs)
    if not rhs_identity:
        return False
    if lhs_identity == rhs_identity:
        return True

    lhs_key = canonical_source_key(lhs)
    rhs_key = canonical_source_key(rhs)
    if not lhs_key or lhs_key != rhs_key:
        return False

    lhs_bare = _is_bare_source_stem(lhs)
    rhs_bare = _is_bare_source_stem(rhs)
    if lhs_bare and rhs_bare:
        return True

    lhs_path = _is_path_like_source(lhs)
    rhs_path = _is_path_like_source(rhs)
    if lhs_bare and rhs_path:
        return True
    if rhs_bare and lhs_path:
        return True
    return False


def short_id(text: str, n: int = 8) -> str:
    return hash_text(text)[:n]


def _dedup_fingerprint(text: str, prefix_len: int = 2000) -> str:
    """Collapse whitespace and take first *prefix_len* chars as a fuzzy key.

    Kept for diagnostics and legacy tests.  Production candidate de-duplication
    no longer uses this fingerprint because long-prefix proof variants can
    differ only at the root-closing line.
    """
    return re.sub(r"\s+", " ", text.strip())[:prefix_len]


def dedup_candidates(candidates: list[str], prefix_len: int = 2000) -> list[str]:
    """De-duplicate only byte-identical proof candidates.

    Prefix/whitespace fingerprints were too strong for proof search: two
    candidates can share a long setup and diverge only at the root-closing
    line.  Exact duplicates have identical Lean behavior in the same context;
    near-duplicates must reach Lean.
    """
    seen_exact: set[str] = set()
    out: list[str] = []
    for c in candidates:
        if c in seen_exact:
            continue
        seen_exact.add(c)
        out.append(c)
    return out


def extract_json_candidates(text: str) -> list[str]:
    if not text:
        return []
    text = extract_final_segment(strip_thoughts(text))
    candidates: list[str] = []
    for block in extract_code_fences(text):
        candidates.append(block.strip())
    _OPEN_CLOSE = {"{": "}", "[": "]"}
    n = len(text)
    i = 0
    while i < n:
        close_ch = _OPEN_CLOSE.get(text[i])
        if close_ch is not None:
            open_ch = text[i]
            depth = 0
            for j in range(i, n):
                if text[j] == open_ch:
                    depth += 1
                elif text[j] == close_ch:
                    depth -= 1
                    if depth == 0:
                        candidates.append(text[i : j + 1])
                        break
            i = j + 1 if depth == 0 else i + 1
        else:
            i += 1
    # de-dup while preserving order
    seen = set()
    out: list[str] = []
    for c in candidates:
        if c in seen:
            continue
        seen.add(c)
        out.append(c)
    return out


def extract_json_object(text: str) -> Optional[str]:
    cands = extract_json_candidates(text)
    return cands[0] if cands else None


_CODE_FENCE_LANGUAGE_TAG_RE = re.compile(r"^[A-Za-z0-9_+-]+$")


def _code_fence_content(text: str, content_start: int, content_end: int) -> str:
    """Return one fence body without its same-line language tag.

    A newline immediately after the opening backticks starts an untagged body;
    its first content line is executable text, even when that line is a single
    identifier such as ``rfl``.  A language tag, by contrast, is written on
    the same line as the opening fence.  Keep that distinction before
    consuming any newline so CRLF and truncated fences follow the same rule.
    """

    content = text[content_start:content_end]
    if content.startswith("\r\n"):
        return content[2:]
    if content.startswith(("\n", "\r")):
        return content[1:]

    line_break = re.search(r"\r\n|[\r\n]", content)
    if line_break is None:
        return content
    opening_line = content[: line_break.start()]
    if _CODE_FENCE_LANGUAGE_TAG_RE.fullmatch(opening_line.strip()):
        return content[line_break.end() :]
    return content


def extract_code_fences(text: str) -> list[str]:
    """
    Extract backtick fenced blocks (3+ backticks, inline or multiline).
    Handles 4+ backtick fences by matching the same-length closing fence.
    If none found, return [].

    When an opening fence has no matching close (e.g. LLM response truncated
    at max_tokens), the remaining text after the fence is still extracted
    rather than silently dropped.
    """
    blocks: list[str] = []
    if "```" not in text:
        return blocks
    i = 0
    n = len(text)
    while i < n:
        start = text.find("```", i)
        if start == -1:
            break
        # Count how many backticks form the opening fence (3, 4, 5, ...)
        fence_len = 3
        while start + fence_len < n and text[start + fence_len] == "`":
            fence_len += 1
        fence = "`" * fence_len
        end = text.find(fence, start + fence_len)
        if end == -1:
            # Unclosed fence — likely max_tokens truncation.
            # Recover the content after the opening fence instead of dropping it.
            content = _code_fence_content(text, start + fence_len, n)
            stripped = content.strip()
            if stripped:
                blocks.append(stripped)
            break
        content = _code_fence_content(text, start + fence_len, end)
        blocks.append(content.strip())
        i = end + fence_len
    return blocks


def proof_looks_truncated(proof: str) -> bool:
    """Heuristic check whether a proof was likely truncated by max_tokens.

    Checks for unbalanced brackets/parens and unclosed ``have``/``let``
    statements without a corresponding body.  Returns True if truncation
    is suspected.
    """
    if not proof:
        return False
    # Check bracket/paren balance
    depth = 0
    i = 0
    while i < len(proof):
        skip_to = _lean_lexical_skip_end(proof, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = proof[i]
        if ch in _GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GROUP_OPEN_TO_CLOSE.values():
            depth -= 1
        i += 1
    if depth > 0:
        return True
    # Check for trailing incomplete have/let (no := or by after it)
    lines = proof.rstrip().split("\n")
    if lines:
        last = lines[-1].strip()
        # Ends mid-expression: trailing operator or comma (ASCII + Unicode)
        if last and last[-1] in (
            ",",
            "+",
            "-",
            "*",
            "/",
            "=",
            ":",
            "→",
            "←",
            "|",
            "≠",
            "∧",
            "∨",
            "≤",
            "≥",
            "↔",
            "⊢",
            "▸",
        ):
            return True
        # Truncated focus-bullet line: ``· <partial_ident>`` where the
        # identifier is too short to be a real tactic (< 3 chars after ·).
        _bullet_m = re.match(r"^[·•]\s*(\S+)$", last)
        if _bullet_m:
            frag = _bullet_m.group(1)
            # Known tactic keywords / identifiers that are NOT truncated
            _VALID_SHORT = frozenset(
                {
                    "by",
                    "do",
                    "at",
                    "on",
                    "rw",
                    "gc",
                    # Common standalone Lean 4 tactics (≤3 chars)
                    "rfl",
                    "ext",
                    "use",
                    "try",
                    "fun",
                    "let",
                    "set",
                    "rel",
                    "red",
                }
            )
            if len(frag) <= 3 and frag not in _VALID_SHORT and not frag.endswith(")"):
                return True
    return False


# Projection on synthetic lemma ref: ``(lemma_XXX args).1`` or ``lemma_XXX.2``
_SYNTH_PROJ_RE = re.compile(
    r"(?:"
    r"\(lemma_[0-9a-f]{16}\b[^)]*\)\.[0-9]+\b"
    r"|"
    r"\blemma_[0-9a-f]{16}\.[0-9]+\b"
    r")"
)

_SYNTHETIC_LEMMA_BASE_RE = re.compile(r"\blemma_[0-9a-f]{6,}(?=[^0-9a-f]|$)")


def proof_has_fragile_projection(proof: str) -> bool:
    """Detect ``first``-combinator proofs that project on synthetic lemma refs.

    The LLM sometimes generates "shotgun probe" proofs::

        by first
        | exact (lemma_XXX _).1
        | exact (lemma_XXX _).2
        | exact lemma_XXX
        ...

    If **all** alternatives fail (common when the proof is injected into a
    different Lean context), the final ``.1``/``.2`` projection error
    ("Invalid projection: Cannot project a value of non-propositional type")
    poisons the *entire* Lean file, causing every candidate check to fail.

    The guard is deliberately narrow:  a ``first`` combinator **must** be
    present; structured proofs that use projection directly (without a
    shotgun ``first``) are left untouched.
    """
    if "first" not in proof:
        return False
    return bool(_SYNTH_PROJ_RE.search(proof))


def synthetic_lemma_refs_in_text(text: str) -> List[str]:
    """Return synthetic lemma base names referenced in Lean text.

    This is intentionally base-name oriented: derived aliases like
    ``lemma_deadbeef__left`` or projections like ``lemma_deadbeef.1`` are
    reported as ``lemma_deadbeef`` so callers can apply provenance guards.
    """
    cleaned = strip_lean_comments(str(text or ""))
    if not cleaned:
        return []
    return list(dict.fromkeys(_SYNTHETIC_LEMMA_BASE_RE.findall(cleaned)))


def extract_final_segment(text: str) -> str:
    if not text:
        return text
    tags = ["final", "answer", "response"]
    for tag in tags:
        m = re.search(rf"<{tag}>(.*?)</{tag}>", text, flags=re.DOTALL | re.IGNORECASE)
        if m:
            return m.group(1).strip()
    marker_re = re.compile(r"(?im)^(final|answer|response)\s*:\s*")
    matches = list(marker_re.finditer(text))
    if matches:
        start = matches[-1].end()
        return text[start:].strip()
    return text


def strip_thoughts(text: str) -> str:
    if not text:
        return text
    # Closed tags: non-greedy match between open and close.
    patterns = [
        r"<think>.*?</think>",
        r"<analysis>.*?</analysis>",
        r"<reasoning>.*?</reasoning>",
        r"<chainofthought>.*?</chainofthought>",
    ]
    out = text
    for pat in patterns:
        out = re.sub(pat, "", out, flags=re.DOTALL | re.IGNORECASE)
    # Unclosed tags (truncated LLM output): strip from the opening tag to EOF.
    out = re.sub(
        r"<(?:think|analysis|reasoning|chainofthought)\b[^>]*>.*",
        "",
        out,
        flags=re.DOTALL | re.IGNORECASE,
    )
    return out


LEAN_TACTIC_HEADS: frozenset[str] = frozenset("""
    simp simpa simp_all simp_rw aesop linarith nlinarith ring omega tauto decide rfl trivial
    norm_num norm_cast push_cast ring_nf field_simp positivity polyrith
    intro intros rintro apply exact have let show suffices obtain
    rw rewrite rwa erw conv calc convert
    case cases rcases match induction constructor left right exfalso split
    ext funext refine refine' use choose existsi
    specialize generalize clear rename subst injection
    assumption contradiction absurd by_contra by_cases push_neg contrapose
    gcongr congr mono
    unfold dsimp change swap rename_i set lift
    mod_cast exact_mod_cast zify ac_rfl abel group
    fin_cases interval_cases mod_cases nontriviality wlog
    continuity measurability fun_prop filter_upwards
    native_decide strong_induction linear_combination noncomm_ring grind prop_complete
    nth_rewrite solve_by_elim
    sorry admit
    """.split())
LEAN_CONTROL_TACTIC_HEADS: frozenset[str] = frozenset(
    ("first", "try", "repeat", "all_goals", "any_goals", "focus")
)
LEAN_QUERY_TACTIC_HEADS: frozenset[str] = frozenset(
    ("exact?", "apply?", "rw?", "simp?", "congr!")
)
LEAN_TACTIC_START_KEYWORDS: tuple[str, ...] = tuple(
    sorted(
        LEAN_TACTIC_HEADS | LEAN_CONTROL_TACTIC_HEADS | LEAN_QUERY_TACTIC_HEADS,
        key=lambda text: (-len(text), text),
    )
)
LEAN_PROOF_SHAPE_KEEP_TOKENS: frozenset[str] = frozenset(
    LEAN_TACTIC_HEADS
    | LEAN_CONTROL_TACTIC_HEADS
    | {"by", "fun", "match", "case", "using"}
)
_TACTIC_KEYWORDS: frozenset[str] = frozenset(
    LEAN_TACTIC_HEADS | LEAN_CONTROL_TACTIC_HEADS
)

# Patterns that indicate English prose rather than Lean tactics.
# These must NOT match valid Lean: single-letter words like `a` are common variable names,
# so require the article to be followed by a multi-letter word (3+ chars) to confirm prose.
_ENGLISH_TACTIC_PATTERNS: list[str] = [
    r"^(have|apply|show|use)\s+(the|this|that|your|my|some|any)\s",
    r"^(have|apply|show|use)\s+an?\s+[a-z]{3,}",
    r"^(let|assume)\s+(me|us)\s",
    r"^introduce\s+(the|a|an|your|our|some|any|each|this|that)\s",
    r"^exactly\s+(the|what|how)",
    r"^cases?\s+(where|when|in\s+which)",
    r"^try\s+(to|and|the)\s",
    r"^first\s+(we|you|let)\s",
]


_LEAN_SYMBOL_RE = re.compile(r"[⟨⟩\[\](){}:=→←↔∀∃λ⊢]|->|=>|≤|≥|≠|∈")
_DECL_START_RE = re.compile(
    r"^(?:theorem|lemma|example|def|abbrev|axiom|instance|class|structure|inductive|"
    r"namespace|section|end|open|import|set_option|variable|variables|noncomputable)\b",
    re.IGNORECASE,
)
_PROSE_HEAD_WORDS: frozenset[str] = frozenset(
    {
        "this",
        "that",
        "these",
        "those",
        "here",
        "there",
        "therefore",
        "hence",
        "because",
        "proof",
        "answer",
        "explanation",
        "output",
        "note",
        "suppose",
        "assume",
        "we",
        "i",
        "you",
        "it",
        "no",
        "hello",
        "hi",
        "thanks",
        # Note: `let` is omitted — it's a valid Lean tactic keyword and has
        # its own specific English pattern (r"^(let|assume)\s+(me|us)\s").
    }
)
_TERM_LINE_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_'.]*(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)*$"
)


def _looks_like_term_proof_expr(text: str) -> bool:
    """Heuristic guard for Lean term-mode proofs (non-`by` expressions)."""
    if not text:
        return False
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    if not lines:
        return False
    first = lines[0]
    first_l = first.lower()

    if _DECL_START_RE.match(first):
        return False
    if first.startswith("--"):
        return False
    if re.match(
        r"^(this|note:|here|we|i|you|it|therefore|remember|output:|explanation:|answer:)\b",
        first,
        re.IGNORECASE,
    ):
        return False

    if first_l.startswith(("fun ", "show ", "match ", "if ")):
        return True
    if _LEAN_SYMBOL_RE.search(first):
        return True

    tok = re.match(r"[A-Za-z_][A-Za-z0-9_'.]*", first)
    if tok:
        head = tok.group(0)
        if head.lower() in _PROSE_HEAD_WORDS:
            return False
        # Single-line identifier/application term (e.g. Nat.add_comm a b).
        if len(lines) == 1 and _TERM_LINE_RE.fullmatch(first):
            return True

    # Multi-line term blocks should contain explicit Lean symbols or lambda/show/match heads.
    return False


def _looks_like_lean_tactic_line(line: str) -> bool:
    """Heuristic: reject lines that look like English sentences rather than Lean tactics."""
    stripped = line.strip()
    if not stripped:
        return False

    # Specific English patterns first (e.g., "have a look", "let me explain").
    for pat in _ENGLISH_TACTIC_PATTERNS:
        if re.match(pat, stripped, re.IGNORECASE):
            return False

    # If the line starts with a known tactic keyword, trust it — valid Lean 4
    # tactics like `intro p q hp hq`, `let x := ...`, `simp only at h`
    # consist entirely of short lowercase words and must not be rejected.
    first_token = re.match(r"[A-Za-z_][A-Za-z0-9_]*", stripped)
    if first_token and first_token.group(0) in _TACTIC_KEYWORDS:
        return True

    if first_token and first_token.group(0).lower() in _PROSE_HEAD_WORDS:
        return False

    # Sentence-ending punctuation suggests natural language (but not ...)
    if stripped.endswith((".", "!", "?")) and not stripped.endswith("..."):
        if not re.search(r"[⟨⟩\[\](){}:=→←↔∀∃λ]", stripped):
            return False

    # Stopword-heavy lines without Lean symbols are likely English prose.
    if not (first_token and first_token.group(0) in _TACTIC_KEYWORDS):
        words = stripped.split()
        if len(words) >= 3 and not _LEAN_SYMBOL_RE.search(stripped):
            lower = stripped.lower()
            if re.search(
                r"\b(the|a|an|this|that|these|those|our|your|my|of|to|in|on|at|for|with|because|therefore|hence)\b",
                lower,
            ):
                return False

    return True


def _extract_tactic_block(text: str) -> str:
    """Extract a tactic block starting with ``by``.

    Keeps indented lines that look like Lean tactics, skipping obvious prose,
    and stops on clear top-level declaration starts or non-lean unindented
    lines. Allows at most 2 consecutive blank lines.
    """
    lines = text.split("\n")
    if not lines:
        return text
    result = [lines[0]]  # the "by ..." line
    blank_run = 0
    for line in lines[1:]:
        stripped = line.strip()
        if not stripped:
            blank_run += 1
            if blank_run > 2:
                break
            result.append(line)
            continue
        blank_run = 0
        # A fresh top-level ``by`` on its own line (indented or not) after the
        # first line is a sibling proof candidate the splitter failed to
        # separate — terminate here rather than absorb it as a tactic line.
        # Because ``by`` is not in ``_TACTIC_KEYWORDS``, the heuristic fallback
        # below would otherwise re-indent it and merge the next block's
        # tactics under it, yielding Lean ``unexpected token 'by'; expected
        # command``. Live trace 1987_b1_21ap_15.jsonl.
        if stripped == "by" or stripped.startswith(("by ", "by\t")):
            break
        # Allow bullet/case lines (Lean syntax)
        if stripped.startswith(("|", "·")) or stripped.startswith("case "):
            result.append(line)
            continue
        # Skip comment lines — they're never needed for Lean compilation
        # and LLMs frequently serialize NL reasoning as Lean comments.
        if stripped.startswith(("--", "/-")):
            continue
        # Indented continuation — keep inside `by` (Lean will validate).
        if line[0] in (" ", "\t"):
            if _looks_like_lean_tactic_line(stripped):
                result.append(line)
            continue
        # Unindented: if this looks like a new top-level declaration, stop.
        # Otherwise, treat it as missing indentation and keep it inside `by`.
        if _DECL_START_RE.match(stripped):
            break
        if _looks_like_lean_tactic_line(stripped):
            result.append("  " + stripped)
            continue
        break
    # Trim trailing blank lines
    while result and not result[-1].strip():
        result.pop()
    return "\n".join(result)


def strip_lean_comments(text: str) -> str:
    """Remove Lean line and block comments from text.

    Handles nested block comments (Lean 4 supports ``/- /- inner -/ outer -/``)
    and line comments (``--``).  Line comments are recognized at depth 0 so
    that ``/-`` appearing inside a ``--`` comment does not open a spurious
    block comment.
    """
    if not text:
        return text
    result: list[str] = []
    i = 0
    n = len(text)
    depth = 0
    while i < n:
        # At depth 0, recognize line comments before block-comment openers so
        # that `-- ... /-` does not start a block comment.
        if depth == 0 and i + 1 < n and text[i] == "-" and text[i + 1] == "-":
            # Skip to end of line.
            j = text.find("\n", i)
            if j == -1:
                break  # rest of text is a line comment
            i = j  # the \n itself is kept (appended below)
            continue
        if i + 1 < n and text[i] == "/" and text[i + 1] == "-":
            depth += 1
            i += 2
        elif i + 1 < n and text[i] == "-" and text[i + 1] == "/" and depth > 0:
            depth -= 1
            i += 2
        else:
            if depth == 0:
                result.append(text[i])
            i += 1
    return "".join(result)


def extract_used_lemmas(proof: str, lemma_names: Sequence[str]) -> List[str]:
    """Extract lemma names that appear in the proof text.

    Prefers full-name matches; falls back to unique short-name matches.
    """
    if not proof or not lemma_names:
        return []
    cleaned = strip_lean_comments(proof)
    used: List[str] = []

    # Full-name matching (names may include dots).
    for name in lemma_names:
        if not name:
            continue
        pattern = r"(?<![A-Za-z0-9_'.])" + re.escape(name) + r"(?![A-Za-z0-9_'])"
        if re.search(pattern, cleaned):
            used.append(name)

    if used:
        return sorted(set(used))

    # Short-name fallback if unique within the context.
    short_map: Dict[str, str] = {}
    duplicates: set[str] = set()
    for name in lemma_names:
        if not name:
            continue
        short = name.split(".")[-1]
        if short in short_map:
            duplicates.add(short)
        else:
            short_map[short] = name
    tokens = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", cleaned))
    for short, full in short_map.items():
        if short in duplicates:
            continue
        if short in tokens:
            used.append(full)
    return sorted(set(used))


def normalize_proof_expr(text: str) -> Optional[str]:
    """
    Convert model output into a Lean proof expression (`by` block or term mode).
    Returns None if we can't find a plausible proof expression.
    """
    s = extract_final_segment(text).strip()
    if not s:
        return None

    s = strip_thoughts(s).strip()
    if not s:
        return None

    if "```" in s:
        s = re.sub(r"```[^\n]*", "", s).strip()

    # Find first line that begins with `by` (preferred - handles tactic blocks correctly).
    m2 = re.search(r"(^|\n)\s*(by\b)", s)
    if m2:
        s = _extract_tactic_block(s[m2.start(2) :]).strip()
    elif not s.strip().startswith("by"):
        # Only if no line starts with `by`: check for theorem definition `:= by`.
        # This avoids matching `:= by` inside `have` statements.
        m = re.search(r":=\s*(by\b)", s)
        if m:
            s = _extract_tactic_block(s[m.start(1) :]).strip()

    # Handle legacy begin/end blocks by converting to `by`.
    if not s.startswith("by") and s.lstrip().startswith("begin"):
        lines = s.strip().splitlines()
        if lines and lines[0].lstrip().startswith("begin"):
            lines = lines[1:]
        while lines and lines[-1].strip() == "end":
            lines.pop()
        s = "by\n" + "\n".join(lines)
        s = _extract_tactic_block(s).strip()

    # Fallback: if it looks like a tactic line, wrap with `by`.
    if not s.startswith("by"):
        lines = s.splitlines()
        for i, line in enumerate(lines):
            stripped = line.strip()
            if not stripped:
                continue
            token = re.match(r"[A-Za-z_][A-Za-z0-9_]*", stripped)
            if (
                token
                and token.group(0) in _TACTIC_KEYWORDS
                and _looks_like_lean_tactic_line(stripped)
            ):
                candidate = "by\n" + "\n".join(lines[i:])
                s = _extract_tactic_block(candidate).strip()
                break

    # Drop any trailing fence-like lines.
    s = re.sub(r"\n\s*```.*$", "", s, flags=re.DOTALL).strip()

    if not s.startswith("by"):
        s = _strip_trailing_prose(s).strip()
        return s if _looks_like_term_proof_expr(s) else None

    # Strip trailing prose that leaked through extraction.
    # Detect where valid Lean tactic block likely ends.
    s = _strip_trailing_prose(s)

    return s


def _strip_trailing_prose(proof: str) -> str:
    """Remove trailing non-Lean content that may have leaked through extraction.

    Conservative approach: only strip lines that are CLEARLY prose, not anything
    that could possibly be valid Lean. Better to keep some prose than break proofs.
    """
    if not proof:
        return proof

    lines = proof.splitlines()

    # Only strip trailing lines that are unambiguously prose
    # (start with common English prose patterns at column 0, no indentation)
    _CLEAR_PROSE = re.compile(
        r"^(?:This\s|Note:|The\s|Here\s|We\s|I\s|You\s|It\s|"
        r"Therefore|Remember|Output:|Explanation:|Answer:)",
        re.IGNORECASE,
    )

    # Find where to cut - scan from end
    cut_at = len(lines)
    for i in range(len(lines) - 1, -1, -1):
        line = lines[i]
        stripped = line.strip()

        # Empty lines - keep scanning
        if not stripped:
            continue

        # Clear prose at start of line (not indented) - this and everything after is prose
        if (
            _CLEAR_PROSE.match(line)
            and not line.startswith(" ")
            and not line.startswith("\t")
        ):
            cut_at = i
            continue

        # This line isn't clear prose - stop scanning
        break

    if cut_at < len(lines):
        return "\n".join(lines[:cut_at]).rstrip()
    return proof


# ------------------------------------------------------------------
# Passive tactic observation (no runtime filtering)
# ------------------------------------------------------------------

_TACTIC_OBS_PATH = Path("runs") / "tactic_observations.jsonl"
_TACTIC_OBS_LOCK = threading.Lock()


def log_tactic_observations(
    proof: str,
    *,
    lemma_name: str = "",
    statement: str = "",
    ok: bool = True,
) -> None:
    """Record unknown tactic tokens from successful `by` proofs.

    This is passive logging only: no auto-promotion or runtime gating.
    """
    if not ok or not proof:
        return
    if not proof.lstrip().startswith("by"):
        return

    def _first_token(line: str) -> Optional[str]:
        cleaned = line.strip()
        if not cleaned:
            return None
        if cleaned.startswith(("--", "/-")):
            return None
        if cleaned.startswith(("|", "·", "•")):
            cleaned = cleaned[1:].strip()
        m = re.match(r"[A-Za-z_][A-Za-z0-9_']*", cleaned)
        if not m:
            return None
        token = m.group(0)
        if len(token) <= 1:
            return None
        if _DECL_START_RE.match(cleaned):
            return None
        if token in _TACTIC_KEYWORDS:
            return None
        return token

    lines = proof.splitlines()
    if len(lines) <= 1:
        return
    unknown: Dict[str, str] = {}
    for line in lines[1:]:
        stripped = line.strip()
        if not stripped:
            continue
        # Harvest only indented or bullet/case lines inside `by` blocks.
        if not (
            line.startswith((" ", "\t"))
            or stripped.startswith(("|", "·", "•", "case "))
        ):
            continue
        token = _first_token(line)
        if token and token not in unknown:
            preview = " ".join(stripped.split())
            if len(preview) > 200:
                preview = preview[:200] + "..."
            unknown[token] = preview

    if not unknown:
        return

    rec_base = {
        "ts": float(now_ts()),
        "lemma": str(lemma_name or ""),
        "statement_hash": short_id(statement, n=12) if statement else "",
        "proof_hash": short_id(proof, n=12),
    }
    try:
        _TACTIC_OBS_PATH.parent.mkdir(parents=True, exist_ok=True)
        with _TACTIC_OBS_LOCK:
            with _TACTIC_OBS_PATH.open("a", encoding="utf-8") as f:
                for token, preview in unknown.items():
                    rec = dict(rec_base)
                    rec["token"] = token
                    rec["line_preview"] = preview
                    f.write(json.dumps(rec, ensure_ascii=False) + "\n")
    except Exception:
        # Passive logging must never break proof flow.
        return


def split_proofs(text: str) -> list[str]:
    """
    Split a response into multiple proof expressions.
    Preferred delimiter: a line exactly '-- PROOF --'. Batch refiner prompts
    also accept '-- BATCH PROOF --' because the client stop sequence uses the
    legacy delimiter.
    """
    raw = text.strip()
    if not raw:
        return []
    parts: list[str] = [raw]
    for delimiter in (
        "\n-- PROOF --\n",
        "\n-- BATCH PROOF --\n",
        "-- PROOF --",
        "-- BATCH PROOF --",
    ):
        parts = [p.strip() for p in raw.split(delimiter) if p.strip()]
        if len(parts) > 1:
            break
    if len(parts) == 1:
        # Some models emit multiple top-level `by ...` blocks without the delimiter.
        # Split on blank lines that precede an unindented `by`.
        parts = [p.strip() for p in re.split(r"\n\s*\n(?=by\b)", raw) if p.strip()]
    if len(parts) == 1:
        # Mixed-format outputs may separate a top-level term-mode proof candidate
        # from a `by` block using blank lines. Split before non-indented lines.
        parts = [p.strip() for p in re.split(r"\n\s*\n(?=[^\s])", raw) if p.strip()]
    if len(parts) == 1 and raw.startswith("by"):
        # Fallback: LLM emitted multiple top-level ``by`` blocks with only a
        # newline (no blank line, no ``-- PROOF --``) between them. Splitting
        # on ``\n(?=by\b)`` recovers them as sibling candidates instead of
        # letting ``_extract_tactic_block`` merge them into a malformed
        # concatenation (live trace 1987_b1_21ap_15.jsonl: 2 parse-error
        # rejects of shape ``by ... \n by ... \n by ...`` producing
        # ``unexpected token 'by'; expected command``).
        parts = [p.strip() for p in re.split(r"\n(?=by\b)", raw) if p.strip()]
    return [p for p in parts if p]


def _extract_proof_from_lean_file(src: str) -> Optional[str]:
    """Extract a `by ...` proof expression from a full Lean file snippet.

    Looks for the last `:= by` occurrence and returns the trailing proof block.
    This helps parse outputs that include full Lean files.
    """
    if not src:
        return None
    matches = list(re.finditer(r":=\s*(by\b)", src))
    if not matches:
        matches = list(re.finditer(r":=\s*\n\s*(by\b)", src))
    if not matches:
        return None
    by_start = matches[-1].start(1)
    snippet = src[by_start:]
    # Drop trailing fenced content (if the model appended another block).
    snippet = re.split(r"\n\s*```", snippet, maxsplit=1)[0]
    # Stop if another top-level declaration starts (rare, but safe).
    lines = snippet.splitlines()
    kept: list[str] = []
    for i, line in enumerate(lines):
        if i > 0 and re.match(r"^\s*(theorem|lemma|example)\b", line):
            break
        kept.append(line)
    snippet = "\n".join(kept).strip()
    return normalize_proof_expr(snippet)


def extract_proof_candidates(text: str) -> list[str]:
    """
    Extract one or more Lean proof expressions from a model response.
    """
    candidates: list[str] = []
    blocks = extract_code_fences(text)
    sources = blocks if blocks else [text]
    for src in sources:
        for chunk in split_proofs(src):
            proof = normalize_proof_expr(chunk)
            if proof:
                candidates.append(proof)
    # If fences existed but yielded nothing, fall back to full text
    if blocks and not candidates:
        for chunk in split_proofs(text):
            proof = normalize_proof_expr(chunk)
            if proof:
                candidates.append(proof)
    # Final fallback: extract proof from full Lean file snippets
    if not candidates:
        sources2 = blocks if blocks else [text]
        for src in sources2:
            proof = _extract_proof_from_lean_file(src)
            if proof:
                candidates.append(proof)
    # Strip Lean comments from candidates — defense-in-depth against NL bleed.
    # Comments never affect compilation but LLMs serialize reasoning as them.
    cleaned: list[str] = []
    for c in candidates:
        stripped_c = strip_lean_comments(c).strip()
        # After stripping comments, re-normalize whitespace: collapse blank runs
        # and ensure the proof still starts with `by`.
        if stripped_c and stripped_c.startswith("by"):
            # Collapse runs of 3+ blank lines into 1
            stripped_c = re.sub(r"\n\s*\n\s*\n", "\n\n", stripped_c)
            cleaned.append(stripped_c)
        elif stripped_c:
            # Lost the `by` prefix after stripping — likely all-comment "proof"
            cleaned.append(c)  # keep original as fallback
    candidates = cleaned if cleaned else candidates
    # De-dup: exact + prefix-based fuzzy (catches max_tokens truncation variants).
    out = dedup_candidates(candidates)
    return out


def normalize_statement(stmt: str) -> str:
    """Canonicalize statement whitespace outside Lean lexical literals.

    Formatting trivia remains cache-equivalent, while whitespace inside
    strings, raw strings, character literals, and quoted identifiers is part
    of the executable proposition and therefore remains byte-for-byte intact.
    """

    s = _canonicalize_big_operator_binders((stmt or "").strip())
    if (
        '"' not in s
        and "«" not in s
        and ("'" not in s or re.search(r"(?<![\w'»])'", s) is None)
    ):
        return re.sub(r"\s+", " ", s).strip()
    out: list[str] = []
    segment_start = 0
    index = 0
    while index < len(s):
        lexical_end = _lean_lexical_skip_end(s, index)
        if lexical_end is None:
            index += 1
            continue
        if segment_start < index:
            out.append(re.sub(r"\s+", " ", s[segment_start:index]))
        lexical = s[index:lexical_end]
        if s.startswith(("/-", "--"), index):
            # Comments are lexical islands for scanning, but their internal
            # whitespace is still formatting trivia for statement identity.
            out.append(re.sub(r"\s+", " ", lexical))
        else:
            out.append(lexical)
        index = lexical_end
        segment_start = index
    if segment_start < len(s):
        out.append(re.sub(r"\s+", " ", s[segment_start:]))
    return "".join(out).strip()


def _split_top_level(stmt: str, sep: str) -> Optional[tuple[str, str]]:
    depth = 0
    i = 0
    while i < len(stmt):
        skip_to = _lean_lexical_skip_end(stmt, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = stmt[i]
        if ch in _GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif depth == 0 and stmt.startswith(sep, i):
            left = stmt[:i].strip()
            right = stmt[i + len(sep) :].strip()
            if left and right:
                return left, right
        i += 1
    return None


_INTRO_PATTERN_DELIMS = {
    "(": ")",
    "[": "]",
    "{": "}",
    "⟨": "⟩",
}


def _is_lean_identifier_start_char(ch: str) -> bool:
    if not ch:
        return False
    return ch == "_" or ch.isalpha()


def _is_lean_identifier_continue_char(ch: str) -> bool:
    if not ch:
        return False
    if ch in {"_", "'"}:
        return True
    if ch.isalnum():
        return True
    return unicodedata.category(ch) in {"Mn", "Mc", "Pc", "Nd", "Nl", "No"}


def _consume_lean_identifier_prefix(text: str) -> str:
    s = str(text or "")
    if not s or not _is_lean_identifier_start_char(s[0]):
        return ""
    idx = 1
    while idx < len(s) and _is_lean_identifier_continue_char(s[idx]):
        idx += 1
    return s[:idx]


def _is_lean_intro_name(token: str) -> bool:
    return bool(token) and _consume_lean_identifier_prefix(token) == token


def _count_binder_names_in_forall_segment(segment: str) -> int:
    """Count binder names inside a single leading `∀ ... ,` segment."""
    rest = str(segment or "").strip()
    count = 0
    while rest:
        if rest[0] in "({[":
            opener = rest[0]
            closer = {"(": ")", "{": "}", "[": "]"}[opener]
            depth = 1
            idx = 1
            while idx < len(rest) and depth > 0:
                if rest[idx] == opener:
                    depth += 1
                elif rest[idx] == closer:
                    depth -= 1
                idx += 1
            if depth != 0:
                return count
            binder_content = rest[1 : idx - 1].strip()
            colon_idx = _first_top_level_colon(binder_content)
            if colon_idx >= 0:
                names = binder_content[:colon_idx].strip()
                count += len(names.split()) if names else 1
            elif binder_content:
                count += 1
            rest = rest[idx:].lstrip()
            continue
        colon_idx = _first_top_level_colon(rest)
        if colon_idx >= 0:
            names = rest[:colon_idx].strip()
            count += len(names.split()) if names else 1
            break
        ident = _consume_lean_identifier_prefix(rest)
        if not ident:
            break
        count += 1
        rest = rest[len(ident) :].lstrip()
        if rest:
            next_is_binder = rest[0] in "({[" or bool(
                _consume_lean_identifier_prefix(rest)
            )
            if not next_is_binder:
                # Lean shorthand such as `∀ a ≥ 2, ...` or `∀ x ∈ s, ...`
                # introduces the binder *and* an immediate hypothesis.
                count += 1
                break
    return count


def _has_top_level_iff(stmt: str) -> bool:
    """Return True if *stmt* contains a top-level ``↔`` or ``<->``."""
    return (
        _split_top_level(stmt, "↔") is not None
        or _split_top_level(stmt, "<->") is not None
    )


def _has_top_level_and_or(stmt: str) -> bool:
    """Return True if *stmt* contains a top-level ``∧`` or ``∨``."""
    return (
        _split_top_level(stmt, "∧") is not None
        or _split_top_level(stmt, "∨") is not None
    )


def _unwrap_single_transparent_parens(statement: str) -> str:
    stripped = str(statement or "").strip()
    if not (stripped.startswith("(") and stripped.endswith(")")):
        return stripped
    inner = stripped[1:-1]
    depth = 0
    balanced = True
    for ch in inner:
        if ch == "(":
            depth += 1
        elif ch == ")":
            if depth == 0:
                balanced = False
                break
            depth -= 1
    if balanced and depth == 0:
        return inner.strip()
    return stripped


def _leading_capacity(
    statement: str,
    *,
    count_lets: bool,
    transparent_lets: bool,
    count_negation_like_head: bool,
) -> int:
    rest = normalize_statement(statement)
    capacity = 0
    while rest:
        unwrapped = _unwrap_single_transparent_parens(rest)
        if unwrapped != rest:
            rest = unwrapped
            continue
        if rest.startswith("∀"):
            tail = rest[1:].lstrip()
            comma_idx = _first_top_level_comma(tail)
            if comma_idx == -1:
                break
            segment = tail[:comma_idx].strip()
            if not segment:
                break
            capacity += _count_binder_names_in_forall_segment(segment)
            rest = tail[comma_idx + 1 :].strip()
            continue
        let_split = _split_top_level_let_body(rest)
        if let_split is not None:
            if count_lets:
                capacity += 1
                rest = let_split[1]
                continue
            if transparent_lets:
                rest = let_split[1]
                continue
            break
        if _has_top_level_iff(rest):
            break
        arrow_split = _split_top_level(rest, "→") or _split_top_level(rest, "->")
        if arrow_split is not None:
            capacity += 1
            rest = arrow_split[1]
            continue
        if _has_top_level_and_or(rest):
            break
        trimmed = rest.lstrip()
        if (
            count_negation_like_head
            and not _has_top_level_iff(trimmed)
            and not _has_top_level_and_or(trimmed)
            and (
                trimmed.startswith("¬")
                or trimmed.startswith("Not ")
                or _split_top_level(trimmed, "≠") is not None
            )
        ):
            capacity += 1
        break
    return capacity


def leading_intro_capacity(statement: str) -> int:
    """Count how many leading ``intro``-style steps a statement can absorb.

    In Lean 4, ``→`` (level 25) binds tighter than ``↔`` (level 20).
    Therefore ``A → B ↔ C`` parses as ``(A → B) ↔ C``, **not**
    ``A → (B ↔ C)``.  An ``→`` whose right-hand side contains a
    top-level ``↔`` is *not* an intro binder — it is the left operand
    of the ``↔``.  We must stop counting at that point.
    """
    return _leading_capacity(
        statement,
        count_lets=True,
        transparent_lets=False,
        count_negation_like_head=True,
    )


def _leading_lambda_capacity(statement: str) -> int:
    """Count how many leading `fun` binders a term proof can absorb."""
    return _leading_capacity(
        statement,
        count_lets=False,
        transparent_lets=False,
        count_negation_like_head=False,
    )


def _leading_structural_blocker_capacity(statement: str) -> int:
    """Count open ∀/→ binders that block constructor/by_contra prefixes."""
    return _leading_capacity(
        statement,
        count_lets=False,
        transparent_lets=True,
        count_negation_like_head=False,
    )


def _proof_prefix_tokens(proof: str) -> list[str]:
    cleaned = strip_lean_comments(str(proof or "")).strip()
    if not cleaned:
        return []
    if cleaned.startswith("by"):
        cleaned = cleaned[2:].lstrip()
    return [token for token in re.split(r"\s+", cleaned) if token]


def leading_intro_demand(proof: str) -> Optional[int]:
    """Count the front-loaded explicit intro demand in a proof prefix.

    Returns ``None`` for complex ``rintro``/pattern forms so callers can avoid
    false-positive filtering on syntax this heuristic does not understand.
    """
    tokens = _proof_prefix_tokens(proof)
    if not tokens:
        return 0
    demand = 0
    saw_intro = False
    intro_heads = {"intro", "intros", "intro!", "intros!", "rintro"}
    idx = 0
    while idx < len(tokens):
        head = tokens[idx].rstrip(";")
        if head not in intro_heads:
            break
        saw_intro = True
        idx += 1
        local = 0
        while idx < len(tokens):
            token = tokens[idx].rstrip(";")
            if token in intro_heads or token.rstrip("!") in _TACTIC_KEYWORDS:
                break
            cleaned = re.sub(r"^[()\[\]{},;]+|[()\[\]{},;]+$", "", token)
            if not cleaned:
                idx += 1
                continue
            opener = token[0] if token else ""
            if opener in _INTRO_PATTERN_DELIMS:
                closer = _INTRO_PATTERN_DELIMS[opener]
                depth = 0
                while idx < len(tokens):
                    chunk = tokens[idx].rstrip(";")
                    for ch in chunk:
                        if ch == opener:
                            depth += 1
                        elif ch == closer:
                            depth -= 1
                    idx += 1
                    if depth <= 0:
                        local += 1
                        break
                else:
                    return None
                continue
            if cleaned == "_" or _is_lean_intro_name(cleaned):
                local += 1
                idx += 1
                continue
            return None
        demand += max(local, 1)
    if not saw_intro:
        return 0
    return demand


def _count_lambda_binder_patterns(head_segment: str) -> int:
    tokens = [tok for tok in re.split(r"\s+", str(head_segment or "").strip()) if tok]
    if not tokens:
        return 1
    count = 0
    idx = 0
    while idx < len(tokens):
        token = tokens[idx].rstrip(";")
        if token == "|":
            idx += 1
            continue
        cleaned = re.sub(r"^[()\[\]{},;]+|[()\[\]{},;]+$", "", token)
        if not cleaned:
            idx += 1
            continue
        opener = token[0] if token else ""
        if opener in _INTRO_PATTERN_DELIMS:
            closer = _INTRO_PATTERN_DELIMS[opener]
            depth = 0
            while idx < len(tokens):
                chunk = tokens[idx].rstrip(";")
                for ch in chunk:
                    if ch == opener:
                        depth += 1
                    elif ch == closer:
                        depth -= 1
                idx += 1
                if depth <= 0:
                    count += 1
                    break
            else:
                return max(count, 1)
            continue
        if cleaned == "_" or _is_lean_intro_name(cleaned):
            count += 1
            idx += 1
            continue
        return max(count, 1)
    return max(count, 1)


def _leading_lambda_prefix_and_demand_from_line(line: str) -> tuple[str, int]:
    stripped = str(line or "").strip()
    if not stripped:
        return "", 0

    wrapper = ""
    for head in ("exact", "refine", "refine'"):
        prefix = f"{head} "
        if stripped.startswith(prefix):
            wrapper = head
            stripped = stripped[len(prefix) :].lstrip()
            break

    while stripped.startswith("("):
        stripped = stripped[1:].lstrip()

    if stripped == "fun":
        prefix = f"{wrapper} fun".strip() if wrapper else "fun"
        return prefix, 1
    if not stripped.startswith("fun "):
        return "", 0

    tail = stripped[len("fun ") :].strip()
    arrow_idx = tail.find("=>")
    head_segment = tail if arrow_idx == -1 else tail[:arrow_idx].strip()
    demand = _count_lambda_binder_patterns(head_segment)
    prefix_parts = [part for part in (wrapper, "fun", head_segment) if part]
    prefix = " ".join(prefix_parts).strip()
    if prefix and arrow_idx != -1:
        prefix = f"{prefix} =>"
    return prefix, demand


def _leading_lambda_demand_with_skippable_prefix(proof: str) -> int:
    lines = _normalized_tactic_lines(proof)
    if not lines:
        return 0
    idx = 0
    while idx < len(lines) and _is_skippable_prefix_line(lines[idx]):
        idx += 1
    if idx >= len(lines):
        return 0
    _prefix, demand = _leading_lambda_prefix_and_demand_from_line(lines[idx])
    return demand


def _leading_intro_demand_with_skippable_prefix(proof: str) -> Optional[int]:
    """Count intro demand after transparent prefix lines like `simp`/`classical`.

    The refiner sometimes emits harmless setup lines before restarting with an
    impossible `intro`. Those lines do not change binder availability, so the
    effective intro prefix should still be rejected.
    """
    lines = _normalized_tactic_lines(proof)
    if not lines:
        return 0
    idx = 0
    while idx < len(lines) and _is_skippable_prefix_line(lines[idx]):
        idx += 1
    intro_lines: list[str] = []
    while idx < len(lines) and _is_intro_like_line(lines[idx]):
        intro_lines.append(lines[idx])
        idx += 1
    if not intro_lines:
        return 0
    synthetic = "by\n  " + "\n  ".join(intro_lines)
    return leading_intro_demand(synthetic)


def starts_with_frontloaded_negation_tactic(proof: str) -> bool:
    """Return True when a proof begins by negating the goal before open binders."""
    tokens = _proof_prefix_tokens(proof)
    if not tokens:
        return False
    head = tokens[0].rstrip(";")
    return head in {"by_contra", "contrapose", "contrapose!"}


def _normalized_tactic_lines(proof: str) -> list[str]:
    cleaned = strip_lean_comments(str(proof or "")).strip()
    if not cleaned:
        return []
    if cleaned.startswith("by"):
        cleaned = cleaned[2:].lstrip()
    out: list[str] = []
    for line in cleaned.splitlines():
        normalized = re.sub(r"^[·|;]+\s*", "", line.strip().rstrip(";"))
        if normalized:
            out.append(normalized)
    return out


def _is_intro_like_line(line: str) -> bool:
    return line.startswith(("intro", "intros", "intro!", "intros!", "rintro"))


def _is_constructor_like_line(line: str) -> bool:
    token = line.split(None, 1)[0] if line else ""
    token = token.rstrip(";")
    return (
        token in ("constructor", "left", "right")
        or line.startswith("refine ⟨")
        or line.startswith("exact ⟨")
    )


def _is_skippable_prefix_line(line: str) -> bool:
    token = line.split(None, 1)[0] if line else ""
    if token in {"classical", "simp", "simp?", "simpa", "simpa?", "haveI", "letI"}:
        return True
    return line.startswith(("set_option ", "open scoped ", "local "))


def starts_with_constructor_like_tactic(proof: str) -> bool:
    """Return True when a constructor tactic appears before any binder intro."""
    for line in _normalized_tactic_lines(proof):
        if _is_intro_like_line(line):
            return False
        if _is_skippable_prefix_line(line):
            continue
        return _is_constructor_like_line(line)
    return False


def starts_with_frontloaded_negation_constructor_conflict(proof: str) -> bool:
    """Return True when a frontloaded negation is followed by constructor-style tactics.

    After `by_contra`/`contrapose`, the immediate goal is no longer an inductive
    constructor target, so tactics like `constructor` or `refine ⟨...⟩` cannot
    possibly apply as the very next structural step.
    """
    lines = _normalized_tactic_lines(proof)
    if not lines:
        return False
    first = lines[0]
    if not first.startswith(("by_contra", "contrapose", "contrapose!")):
        return False
    for line in lines[1:]:
        if _is_skippable_prefix_line(line):
            continue
        if _is_constructor_like_line(line):
            return True
        return False
    return False


def leading_binder_shape_issue(proof: str, statement: str) -> Optional[str]:
    """Return a reason when a proof prefix is incompatible with a goal shape."""
    normalized_statement = (
        normalize_subgoal_statement(statement) or str(statement or "").strip()
    )
    intro_capacity = leading_intro_capacity(normalized_statement)
    lambda_capacity = _leading_lambda_capacity(normalized_statement)
    structural_blockers = _leading_structural_blocker_capacity(normalized_statement)
    intro_demand = _leading_intro_demand_with_skippable_prefix(proof)
    if intro_demand is not None and intro_demand > intro_capacity:
        return "intro_demand_exceeds_capacity"
    lambda_demand = _leading_lambda_demand_with_skippable_prefix(proof)
    if lambda_demand > lambda_capacity:
        return "intro_demand_exceeds_capacity"
    if starts_with_frontloaded_negation_tactic(proof) and structural_blockers > 0:
        return "frontloaded_negation_with_open_binders"
    if starts_with_constructor_like_tactic(proof) and structural_blockers > 0:
        return "constructor_before_open_binders"
    return None


def _analyze_top_level_focus_markers(proof: str) -> tuple[bool, bool]:
    cleaned = strip_lean_comments(str(proof or "")).strip()
    if not cleaned.startswith("by"):
        return False, False

    def _indent_width(line: str) -> int:
        return len(line) - len(line.lstrip(" \t"))

    def _is_focus_marker(line: str) -> bool:
        stripped = str(line or "").strip()
        return stripped.startswith(("·", "•", "|")) or stripped.startswith("case ")

    def _unwrap_focus_scope_wrappers(line: str) -> str:
        stripped = str(line or "").strip()
        while True:
            wrapper = re.match(r"^(?:repeat'?)\s+(.+)$", stripped)
            if wrapper is None:
                return stripped
            stripped = wrapper.group(1).strip()

    def _opens_focus_scope(line: str) -> bool:
        stripped = _unwrap_focus_scope_wrappers(line)
        if not stripped:
            return False
        if stripped.startswith("first |"):
            return True
        if re.match(r"^(?:have|let)\b.*:=\s*by\s*$", stripped):
            return True
        token = stripped.split(None, 1)[0].rstrip(";")
        if token in {
            "apply",
            "by_cases",
            "cases",
            "cases'",
            "constructor",
            "first",
            "induction",
            "induction'",
            "left",
            "obtain",
            "rcases",
            "right",
            "split",
        }:
            return True
        if token in {"refine", "refine'"}:
            if "?_" in stripped or re.search(r"\?[A-Za-z0-9_']+", stripped):
                return True
            if re.search(r"(?<![A-Za-z0-9_'])_(?![A-Za-z0-9_'])", stripped):
                return True
            return False
        if stripped == "fun" or stripped.endswith(" fun"):
            return True
        return stripped.endswith(" with") or " with " in stripped

    lines = cleaned.splitlines()
    if not lines:
        return False, False

    first = lines[0].strip()
    if not first.startswith("by"):
        return False, False
    remainder = first[2:].strip()
    if remainder:
        has_focus_marker = _is_focus_marker(remainder)
        return has_focus_marker, has_focus_marker

    top_level_indent: Optional[int] = None
    focus_scope_open = False
    has_focus_marker = False
    for line in lines[1:]:
        stripped = line.strip()
        if not stripped:
            continue
        indent = _indent_width(line)
        if top_level_indent is None:
            top_level_indent = indent
        if indent != top_level_indent:
            continue
        if _is_focus_marker(stripped):
            has_focus_marker = True
            if not focus_scope_open:
                return has_focus_marker, True
            continue
        focus_scope_open = _opens_focus_scope(stripped)
    return has_focus_marker, False


def proof_has_top_level_focus_marker(proof: str) -> bool:
    return _analyze_top_level_focus_markers(proof)[0]


def proof_top_level_focus_line_numbers(proof: str) -> set[int]:
    """Return 1-based proof line numbers for top-level focus-marker lines."""
    lines = str(proof or "").splitlines()
    if not lines:
        return set()

    first = lines[0].strip()
    if not first.startswith("by"):
        return set()

    def _indent_width(line: str) -> int:
        return len(line) - len(line.lstrip(" \t"))

    def _is_focus_marker(line: str) -> bool:
        stripped = str(line or "").strip()
        return stripped.startswith(("·", "•", "|")) or stripped.startswith("case ")

    focus_lines: set[int] = set()
    remainder = first[2:].strip()
    if remainder and _is_focus_marker(remainder):
        focus_lines.add(1)

    top_level_indent: Optional[int] = None
    for index, line in enumerate(lines[1:], start=2):
        stripped = re.sub(r"--.*$", "", line).strip()
        if not stripped:
            continue
        indent = _indent_width(line)
        if top_level_indent is None:
            top_level_indent = indent
        if indent != top_level_indent:
            continue
        if _is_focus_marker(stripped):
            focus_lines.add(index)
    return focus_lines


def proof_last_top_level_line_is_focus_marker(proof: str) -> bool:
    lines = str(proof or "").splitlines()
    if not lines:
        return False

    first = lines[0].strip()
    if not first.startswith("by"):
        return False

    def _indent_width(line: str) -> int:
        return len(line) - len(line.lstrip(" \t"))

    entries: list[str] = []
    remainder = first[2:].strip()
    if remainder:
        entries.append(remainder)

    top_level_indent: Optional[int] = None
    for line in lines[1:]:
        stripped = re.sub(r"--.*$", "", line).strip()
        if not stripped:
            continue
        indent = _indent_width(line)
        if top_level_indent is None:
            top_level_indent = indent
        if indent != top_level_indent:
            continue
        entries.append(stripped)

    if not entries:
        return False
    last = entries[-1]
    return last.startswith(("·", "•", "|")) or last.startswith("case ")


def proof_has_orphan_top_level_focus_marker(proof: str) -> bool:
    """Return True when a `by` proof contains orphan top-level focus markers.

    Iterative refiners sometimes emit patch-style continuations such as
    ``by · ...`` or ``by case ...`` that only make sense if an earlier
    branch-opening tactic is still in scope. We always check each candidate as
    a fresh standalone proof, so top-level focus markers must be justified by
    earlier top-level tactics in the same `by` block.
    """
    return _analyze_top_level_focus_markers(proof)[1]


def is_reflexive_statement(stmt: str) -> bool:
    eq = _split_top_level(stmt, "=") or _split_top_level(stmt, "↔")
    if not eq:
        return False
    left, right = eq
    return normalize_statement(left) == normalize_statement(right)


def is_trivial_proof(proof: str) -> bool:
    s = proof.strip()
    if not s.startswith("by"):
        return False
    s = s[2:].strip()
    s = re.sub(r"^exact\s+", "", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s in {"rfl", "simp", "simp?", "decide", "trivial"}


_LEAN_METAVARIABLE_RE = re.compile(
    r"\?(?:_|[A-Za-z\u0370-\u03FF][A-Za-z0-9_'.\u0370-\u03FF]*)",
    re.IGNORECASE,
)
_PLACEHOLDER_RE = re.compile(
    rf"\b(?:sorry|admit)\b|{_LEAN_METAVARIABLE_RE.pattern}",
    re.IGNORECASE,
)
_SORRY_ADMIT_RE = re.compile(r"\b(?:sorry|admit)\b", re.IGNORECASE)


def _strip_lean_noncode_for_pattern_checks(text: str) -> str:
    """Remove comments and string literal contents before token heuristics."""
    from .math_utils import _strip_lean_comments_and_strings

    stripped, lexically_closed = _strip_lean_comments_and_strings(str(text or ""))
    if not lexically_closed:
        return str(text or "")
    return _mask_lean_quoted_identifiers(stripped)


def _mask_lean_quoted_identifiers(text: str) -> str:
    """Mask escaped Lean identifiers so keyword scans see only code tokens."""

    raw = str(text or "")
    out: list[str] = []
    index = 0
    while index < len(raw):
        if raw[index] != "«":
            out.append(raw[index])
            index += 1
            continue
        end = _lean_lexical_skip_end(raw, index)
        if end is None or end <= index:
            return raw
        out.append(" " * (end - index))
        index = end
    return "".join(out)


def strip_lean_comments_and_string_literals(text: str) -> str:
    """Remove non-code text before lightweight Lean identifier scans.

    An unterminated comment/string fails closed by returning the original text;
    callers then retain extra dependencies rather than silently dropping code.
    """

    from .math_utils import _strip_lean_comments_and_strings

    stripped, lexically_closed = _strip_lean_comments_and_strings(str(text or ""))
    return stripped if lexically_closed else str(text or "")


def strip_lean_noncode_for_token_checks(text: str) -> str:
    """Remove comments, literals, and escaped identifiers before keyword scans."""

    stripped = strip_lean_comments_and_string_literals(text)
    return _mask_lean_quoted_identifiers(stripped)


def contains_metavariable_placeholder(text: str) -> bool:
    """Return True when Lean metavariable placeholders appear in code positions."""
    stripped = _strip_lean_noncode_for_pattern_checks(text)
    return _LEAN_METAVARIABLE_RE.search(stripped) is not None


def has_placeholder_tactics(proof: str) -> bool:
    stripped = _strip_lean_noncode_for_pattern_checks(proof)
    return _PLACEHOLDER_RE.search(stripped) is not None


def has_sorry_or_admit(proof: str) -> bool:
    """Return True when an otherwise-valid proof uses unsound placeholders.

    Lean accepts `sorry` (and sometimes `admit`) as a proof term, so even
    when Lean reports `ok=True`, we treat these as materialization-incompatible.
    """
    stripped = _strip_lean_noncode_for_pattern_checks(proof)
    return _SORRY_ADMIT_RE.search(stripped) is not None


def count_sorry_admit_holes(proof: str) -> int:
    """Count sorry/admit hole occurrences in code positions.

    Uses the same canonical detection as :func:`has_sorry_or_admit`:
    strips Lean comments and string literals, then matches
    ``sorry`` and ``admit`` (case-insensitive, word-boundary).
    """
    stripped = _strip_lean_noncode_for_pattern_checks(proof)
    return len(_SORRY_ADMIT_RE.findall(stripped))


def has_materialization_incompatible_placeholders(
    proof: str,
    *,
    validated_complete: bool = False,
) -> bool:
    """Return True when placeholder syntax makes a proof unsafe to materialize.

    `sorry`/`admit` are always unsafe because they are unsound completion
    markers. Lean metavariable syntax like `?_` can be a strategic tactic-hole
    surface form, so it is only treated as materialization-incompatible when
    the proof has not already been validated as complete.
    """
    if has_sorry_or_admit(proof):
        return True
    stripped = _strip_lean_noncode_for_pattern_checks(proof)
    if re.search(r"\bexact\s+\?[A-Za-z_][A-Za-z0-9_']*|\bexact\s+\?_", stripped):
        return True
    # Named metavariables are references to unresolved elaborator state, not
    # the anonymous tactic holes that ``refine ... ?_`` deliberately opens and
    # later bullet blocks may close.  They remain unsafe even when the enclosing
    # helper arrived through a trusted execution checkpoint.
    if re.search(r"\?[A-Za-z\u0370-\u03FF][A-Za-z0-9_'.\u0370-\u03FF]*", stripped):
        return True
    # A standalone `_` in term-producing tactic positions is an elaborator
    # hole too. Keep qualified names such as `_root_.h` and wildcard patterns
    # outside these term positions valid.
    if re.search(
        r"\b(?:exact|refine|apply|using|from)\s+\(*\s*"
        r"(?<![A-Za-z0-9_'])_(?![A-Za-z0-9_'])",
        stripped,
    ) or re.fullmatch(r"\s*(?:by\s+)?_\s*", stripped):
        return True
    if validated_complete:
        return False
    return contains_metavariable_placeholder(proof)


# Patterns that often cause goal explosion or logical dead ends
_RISKY_TACTIC_PATTERNS = [
    (r"repeat['']?\s+constructor", "repeat_constructor"),
    (r"repeat['']?\s+cases", "repeat_cases"),
    (r"repeat['']?\s+induction", "repeat_induction"),
    (r"exfalso\s*$", "exfalso_terminal"),  # exfalso at end with nothing after
    (r"constructor\s*\n\s*constructor", "nested_constructor"),
]

_RISKY_PATTERN_REGEXES = [
    (re.compile(p, re.IGNORECASE), name) for p, name in _RISKY_TACTIC_PATTERNS
]


def detect_risky_tactics(proof: str) -> list[str]:
    """Detect tactic patterns that often lead to goal explosion or dead ends.

    Returns a list of detected risky pattern names (empty if none found).
    These patterns are not necessarily wrong, but correlate with proof failures.
    """
    found = []
    for regex, name in _RISKY_PATTERN_REGEXES:
        if regex.search(proof):
            found.append(name)
    return found


# Degenerate proof patterns that can NEVER succeed on ANY goal.
# These are hard-filtered (rejected outright), not just deprioritized.
_DEGENERATE_PROOF_PATTERNS = [
    # False.elim.symm — .symm cannot apply to the elimination form.
    # Lean 4 type error: "invalid field 'symm'" on (False → α).
    re.compile(r"\bFalse\.elim\.symm\b"),
    # Projection and eliminator functions do not expose `.symm`.
    re.compile(
        r"\b(?:[A-Za-z_][A-Za-z0-9_']*\.)+(?:mp|mpr|elim|rec|recOn|casesOn)\.symm\b"
    ),
    # Propositional constructors without symmetric structure can never expose `.symm`.
    re.compile(r"\b(?:True|False)\.symm\b"),
    # Bare "False" as the entire proof body — never a valid term-mode proof.
    re.compile(r"^\s*False\s*$"),
    # exfalso immediately followed by exact False.elim without a hypothesis —
    # False.elim needs a proof of False; without one this is always a type error.
    # We match "exfalso" + "exact False.elim" with NO variable/hypothesis arg,
    # only allowing (by trivial), (by decide), .symm, or nothing — all nonsensical.
    re.compile(
        r"\bexfalso\b\s*\n\s*\bexact\s+False\.elim\s*"
        r"(?:\.symm\b|\(by\s+(?:trivial|decide)\)|\s*$)",
        re.MULTILINE,
    ),
]


def is_degenerate_proof(proof: str) -> bool:
    """Return True if the proof uses a pattern that can NEVER succeed.

    These patterns are structurally invalid regardless of context — no
    false-positive risk.  Matched after comment stripping.
    """
    if starts_with_frontloaded_negation_constructor_conflict(proof):
        return True
    cleaned = strip_lean_comments(str(proof or ""))
    for pat in _DEGENERATE_PROOF_PATTERNS:
        if pat.search(cleaned):
            return True
    return False


# ── Dot-notation allowlist gate ─────────────────────────────────────
# Safe local/synthetic projections are intentionally narrow: only
# `.1`, `.2`, `.mp`, and `.mpr` are admitted without extra Lean-backed
# evidence. Everything else must either be a known constructor/global
# decl path or is rejected as an unverified projection chain.

_DOT_GATE_SAFE_PROJECTION_SUFFIXES: frozenset[str] = frozenset(
    {
        "1",
        "2",
        "mp",
        "mpr",
    }
)

_DOT_GATE_CONSTRUCTOR_SAFE: frozenset[str] = frozenset(
    {
        "intro",
        "mk",
        "refl",
        "rec",
        "recOn",
        "casesOn",
        "ndrec",
        "ndrecOn",
        "elim",
        "some",
        "none",
        "inl",
        "inr",
        "nil",
        "cons",
        "succ",
        "zero",
        "isTrue",
        "isFalse",
    }
)

# Synthetic lemma bases are system-generated and always in scope.
_DOT_GATE_SYNTHETIC_BASE_RE = re.compile(
    r"^(?:lemma_[0-9a-f]{6,}|putnam_\d{4}_[a-z]\d)$",
)


def _iter_dot_gate_tokens(text: str) -> list[str]:
    """Return dotted tokens, including numeric projection segments."""
    tokens: list[str] = []
    seen: set[str] = set()
    n = len(text)
    i = 0
    while i < n:
        ch = text[i]
        if not (ch.isalpha() or ch == "_"):
            i += 1
            continue
        if i > 0 and (text[i - 1].isalnum() or text[i - 1] in "_'"):
            i += 1
            continue
        j = i + 1
        while j < n and (text[j].isalnum() or text[j] in "_'"):
            j += 1
        parts = [text[i:j]]
        k = j
        saw_dot = False
        while k < n and text[k] == ".":
            part_start = k + 1
            if part_start >= n:
                break
            next_ch = text[part_start]
            if not (next_ch.isalpha() or next_ch == "_" or next_ch.isdigit()):
                break
            part_end = part_start + 1
            while part_end < n and (text[part_end].isalnum() or text[part_end] in "_'"):
                part_end += 1
            parts.append(text[part_start:part_end])
            k = part_end
            saw_dot = True
        if saw_dot:
            token = ".".join(parts)
            if token not in seen:
                seen.add(token)
                tokens.append(token)
            i = k
            continue
        i = j
    return tokens


def _dot_gate_safe_projection_base(token: str) -> str:
    parts = [part for part in str(token or "").split(".") if part]
    if len(parts) < 2:
        return ""
    idx = len(parts)
    while idx > 1 and parts[idx - 1] in _DOT_GATE_SAFE_PROJECTION_SUFFIXES:
        idx -= 1
    if idx == len(parts):
        return ""
    return ".".join(parts[:idx])


def unsafe_dot_projections(
    proof: str,
    *,
    allowed_projection_bases: Optional[Sequence[str]] = None,
) -> list[str]:
    """Return dotted identifiers whose suffix chain is not structurally safe.

    Safe projection tails are limited to `.1`, `.2`, `.mp`, and `.mpr`.
    Two-part uppercase namespace refs are left alone because global scope
    checking already validates them elsewhere. When *allowed_projection_bases*
    is provided, any non-allowlisted tail on those known-local/synthetic bases
    is rejected even if the base name would otherwise look harmless.
    """
    cleaned = _strip_lean_noncode_for_pattern_checks(str(proof or ""))
    if not cleaned:
        return []

    authorized_bases = {
        str(base or "").strip()
        for base in (allowed_projection_bases or [])
        if str(base or "").strip()
    }
    flagged: list[str] = []
    for token in _iter_dot_gate_tokens(cleaned):
        parts = token.split(".")
        if len(parts) < 2:
            continue

        base_root = parts[0]
        suffix = parts[-1]
        safe_base = _dot_gate_safe_projection_base(token)
        if safe_base:
            if safe_base in authorized_bases:
                continue
            if _DOT_GATE_SYNTHETIC_BASE_RE.fullmatch(safe_base):
                continue
            if "." not in safe_base and base_root[:1].islower():
                continue

        if len(parts) == 2 and base_root[:1].isupper() and suffix in _DOT_GATE_CONSTRUCTOR_SAFE:
            continue

        if len(parts) == 2 and len(base_root) >= 2 and base_root[:1].isupper():
            continue

        if (
            len(parts) == 2
            and len(base_root) == 1
            and base_root.isupper()
            and suffix in _DOT_GATE_SAFE_PROJECTION_SUFFIXES
        ):
            continue

        if len(base_root) == 1 and base_root.isupper():
            flagged.append(token)
            continue

        if base_root[:1].islower():
            flagged.append(token)
            continue

        if len(parts) >= 3 and suffix not in _DOT_GATE_SAFE_PROJECTION_SUFFIXES:
            flagged.append(token)
            continue

    return flagged


def passes_consistency_filter(proof: str) -> bool:
    """Cheap syntactic sanity checks to discard obviously invalid proofs."""
    if not proof or not proof.strip():
        return False
    # Require full balance; partially balanced proofs still hide real syntax errors.
    return _balance_score(proof) >= 1.0


def _balance_score(text: str) -> float:
    # Canonical implementation lives in math_utils.balance_score.
    from .math_utils import balance_score

    return balance_score(text)


def looks_like_lean_type(s: str) -> bool:
    """Heuristic: does this string look like a Lean 4 type expression?

    Rejects natural-language strings (advice, instructions, prose) that
    models sometimes emit instead of formal Lean types.
    """
    if not s or len(s) < 3:
        return False

    # Reject strings containing Lean metavariable placeholders (for example
    # `?_`, `?m.123`, `?m_1`, `?foo`) in code positions. These are internal
    # elaboration artifacts, not valid standalone types.
    if contains_metavariable_placeholder(s):
        return False

    # Must contain at least one Lean-like token.
    # Note: a bare ":" is NOT sufficient — English sentences ending with ":"
    # (e.g. "Let's think of the mathematical content:") would false-positive.
    # We require " : " (type annotation) or other strong indicators.
    _LEAN_INDICATORS = (
        " : ",
        " := ",
        "=",
        ">",
        "<",
        "∀",
        "∃",
        "→",
        "↔",
        "∧",
        "∨",
        "¬",
        "ℕ",
        "ℤ",
        "ℝ",
        "ℚ",
        "ℂ",
        "Nat",
        "Int",
        "Real",
        "Float",
        "∈",
        "⊆",
        "⊂",
        "≤",
        "≥",
        "∣",
        "∤",
        "theorem ",
        "lemma ",
        "Prop",
        "Type",
        "Sort",
        "Even",
        "Odd",
        "Prime",
        "Continuous",
        "Differentiable",
        "Integrable",
        "Measurable",
        "Summable",
        "Tendsto",
        "Filter",
        "Set.Icc",
        "Set.Ico",
        "Finset",
        "Multiset",
        "List",
        "Vector",
    )
    if not any(ind in s for ind in _LEAN_INDICATORS):
        return False

    # Reject strings that look like natural-language sentences.
    lower = s.lower().strip()
    _NL_PREFIXES = (
        "check ",
        "verify ",
        "show ",
        "prove ",
        "ensure ",
        "note ",
        "consider ",
        "assume ",
        "let us ",
        "let's ",
        "let me ",
        "use ",
        "apply ",
        "the ",
        "this ",
        "that ",
        "if ",
        "when ",
        "for each ",
        "we need",
        "we can",
        "we have",
        "we are",
        "we might",
        "we note",
        "we want",
        "we will",
        "we see",
        "we know",
        "we must",
        "it follows",
        "by ",
        "since ",
        "because ",
        "observe ",
        "recall ",
        "first ",
        "next ",
        "then ",
        "finally ",
        "in order",
        "to show",
        "to prove",
        "make sure",
        "determine ",
        "given ",
        "hence ",
        "thus ",
        "therefore ",
        "obviously ",
        "clearly ",
        "notice ",
        "remember ",
        "suppose ",
        "according ",
        "try ",
        "start ",
        "begin ",
        "now ",
        "also ",
        "but ",
        "so we",
        "so ",
        "here ",
        "below ",
        "above ",
        "following ",
    )
    if any(lower.startswith(p) for p in _NL_PREFIXES):
        return False

    # Reject if predominantly English words (>4 words of 3+ chars)
    # with fewer than 2 Lean structural markers (excluding trailing colon).
    words = re.findall(r"[A-Za-z]{3,}", s)
    # Don't count a trailing colon as a structural marker — prose headers
    # like "Mathematical content:" would get +1 from the colon.
    s_for_struct = s.rstrip().rstrip(":")
    lean_struct = sum(1 for c in s_for_struct if c in ":=∀∃→↔∧∨¬≤≥⊆∈∣()[]{}.,<>")
    if len(words) > 4 and lean_struct < 2:
        return False
    # Reject truncated types: unbalanced parentheses/brackets indicate the
    # string was cut off mid-expression (e.g. by max_tokens).
    depth_paren = 0
    depth_bracket = 0
    depth_brace = 0
    for ch in s:
        if ch == "(":
            depth_paren += 1
        elif ch == ")":
            depth_paren -= 1
        elif ch == "[":
            depth_bracket += 1
        elif ch == "]":
            depth_bracket -= 1
        elif ch == "{":
            depth_brace += 1
        elif ch == "}":
            depth_brace -= 1
    if depth_paren != 0 or depth_bracket != 0 or depth_brace != 0:
        return False
    return True


_STANDALONE_SORT_LIKE_RE = re.compile(
    r"^\s*(?:"
    r"Prop"
    r"|Type(?:\s+(?:\*|_|[A-Za-z0-9_'.]+|\([^)]*\)))?"
    r"|Sort(?:\s+(?:\*|_|[A-Za-z0-9_'.]+|\([^)]*\)))?"
    r")\s*$"
)


def is_standalone_sort_like_lean_expr(s: str) -> bool:
    """Return True for bare universe/sort expressions such as ``Prop``."""
    rendered = re.sub(r"\s+", " ", str(s or "").strip())
    if not rendered:
        return False
    return bool(_STANDALONE_SORT_LIKE_RE.fullmatch(rendered))


_LEAN_QUOTED_IDENTIFIER_PATTERN = r"«[^»\n]+»"
_LEAN_IDENTIFIER_TOKEN_PATTERN = (
    rf"{_LEAN_QUOTED_IDENTIFIER_PATTERN}"
    r"|[A-Za-z_\u0370-\u03FF][A-Za-z0-9_'.✝\u0370-\u03FF]*"
)
_LEAN_IDENTIFIER_TOKEN_RE = re.compile(_LEAN_IDENTIFIER_TOKEN_PATTERN)
_LEAN_IDENTIFIER_FOLLOW_PATTERN = r"(?=$|\s|[:=,;\)\]\}])"
_LEAN_ATOM_TOKEN_RE = re.compile(
    rf"{_LEAN_IDENTIFIER_TOKEN_PATTERN}|[ℕℤℚℝℂ]"
)
_PROP_PLACEHOLDER_ATOM_RE = re.compile(r"[A-Z](?:[0-9_']*)")
_NON_THEOREM_PROPOSITION_MARKERS = (
    "∀",
    "∃",
    "¬",
    "↔",
    "∧",
    "∨",
    "∈",
    "∉",
    "⊆",
    "⊂",
    "⊇",
    "⊃",
    "∣",
    "∤",
    "≤",
    "≥",
    "≠",
    " = ",
    " < ",
    " > ",
    ".Finite",
    ".Infinite",
    ".Nonempty",
    "Set.MapsTo ",
    "Set.InjOn ",
    "Set.SurjOn ",
    "Set.BijOn ",
    "Filter.Tendsto ",
    "Function.Injective ",
    "Function.Surjective ",
    "Function.Bijective ",
    "Function.LeftInverse ",
    "Function.RightInverse ",
)
_NON_THEOREM_TYPE_HEADS = {
    "nat",
    "int",
    "rat",
    "real",
    "complex",
    "bool",
    "string",
    "char",
    "unit",
    "punit",
    "empty",
    "set",
    "finset",
    "multiset",
    "list",
    "array",
    "vector",
    "subtype",
    "matrix",
    "filter",
    "topologicalspace",
    "metricspace",
    "measure",
    "measurespace",
}


def _strip_wrapping_delimiters_for_non_theorem_check(expr: str) -> str:
    rendered = str(expr or "").strip()
    pairs = {"(": ")", "[": "]", "{": "}"}
    while (
        len(rendered) >= 2
        and rendered[0] in pairs
        and rendered[-1] == pairs[rendered[0]]
    ):
        opener = rendered[0]
        closer = pairs[opener]
        depth = 0
        balanced = True
        for idx, ch in enumerate(rendered):
            if ch == opener:
                depth += 1
            elif ch == closer:
                depth -= 1
            if depth == 0 and idx != len(rendered) - 1:
                balanced = False
                break
        if not balanced or depth != 0:
            break
        rendered = rendered[1:-1].strip()
    return rendered


def _head_token_for_non_theorem_check(expr: str) -> str:
    rendered = _strip_wrapping_delimiters_for_non_theorem_check(expr)
    match = _LEAN_ATOM_TOKEN_RE.search(rendered)
    return match.group(0) if match else ""


def _binder_name_sets_for_non_theorem_check(
    binders: Sequence[str],
) -> tuple[Set[str], Set[str]]:
    declared_names: Set[str] = set()
    prop_names: Set[str] = set()
    for seg in binders:
        raw = _strip_wrapping_delimiters_for_non_theorem_check(str(seg or "").strip())
        if not raw:
            continue
        colon_idx = _first_top_level_colon(raw)
        if colon_idx < 0:
            continue
        binder_names = raw[:colon_idx].strip()
        binder_type = _strip_wrapping_delimiters_for_non_theorem_check(
            raw[colon_idx + 1 :].strip()
        )
        names_in_segment: Set[str] = set()
        for token in re.split(r"\s+", binder_names):
            cleaned = str(token or "").strip().strip(",")
            cleaned = cleaned.strip("()[]{}")
            if cleaned and _LEAN_ATOM_TOKEN_RE.fullmatch(cleaned):
                names_in_segment.add(cleaned)
        declared_names.update(names_in_segment)
        if normalize_statement(binder_type) == "Prop":
            prop_names.update(names_in_segment)
    return declared_names, prop_names


def _contains_obvious_proposition_structure(rendered: str) -> bool:
    if any(marker in rendered for marker in _NON_THEOREM_PROPOSITION_MARKERS):
        return True
    if re.search(r"(?<![:<>=!])=(?!=)", rendered):
        return True
    if "<=" in rendered or ">=" in rendered:
        return True
    if re.search(r"(?<![-=])>", rendered):
        return True
    if re.search(r"<(?![-=])", rendered):
        return True
    return False


def _obviously_proposition_like_lean_expr(
    expr: str,
    *,
    prop_binder_names: Optional[Set[str]] = None,
    bound_binder_names: Optional[Set[str]] = None,
) -> bool:
    rendered = re.sub(
        r"\s+", " ", _strip_wrapping_delimiters_for_non_theorem_check(expr)
    )
    if not rendered:
        return False
    binders, body = _split_leading_forall_statement(rendered)
    if binders:
        declared_names, prop_names = _binder_name_sets_for_non_theorem_check(binders)
        return _obviously_proposition_like_lean_expr(
            body,
            prop_binder_names=set(prop_binder_names or set()) | prop_names,
            bound_binder_names=set(bound_binder_names or set()) | declared_names,
        )

    prop_names = set(prop_binder_names or set())
    bound_names = set(bound_binder_names or set())
    if rendered in prop_names:
        return True
    if rendered not in bound_names and _PROP_PLACEHOLDER_ATOM_RE.fullmatch(rendered):
        return True

    lower = rendered.lower()
    if lower in {"true", "false"}:
        return True
    if rendered.startswith("¬"):
        return _obviously_proposition_like_lean_expr(
            rendered[1:].strip(),
            prop_binder_names=prop_names,
            bound_binder_names=bound_names,
        )
    if lower.startswith("not "):
        return _obviously_proposition_like_lean_expr(
            rendered[4:].strip(),
            prop_binder_names=prop_names,
            bound_binder_names=bound_names,
        )
    if _contains_obvious_proposition_structure(rendered):
        return True

    split_arrow = _split_top_level(rendered, "→") or _split_top_level(rendered, "->")
    if split_arrow is not None:
        _left, right = (str(part or "").strip() for part in split_arrow)
        return _obviously_proposition_like_lean_expr(
            right,
            prop_binder_names=prop_names,
            bound_binder_names=bound_names,
        )
    return False


def _is_non_theorem_standalone_lean_expr_inner(
    expr: str,
    *,
    prop_binder_names: Optional[Set[str]] = None,
    bound_binder_names: Optional[Set[str]] = None,
) -> bool:
    rendered = re.sub(
        r"\s+", " ", _strip_wrapping_delimiters_for_non_theorem_check(expr)
    )
    if not rendered:
        return False
    binders, body = _split_leading_forall_statement(rendered)
    if binders:
        declared_names, prop_names = _binder_name_sets_for_non_theorem_check(binders)
        return _is_non_theorem_standalone_lean_expr_inner(
            body,
            prop_binder_names=set(prop_binder_names or set()) | prop_names,
            bound_binder_names=set(bound_binder_names or set()) | declared_names,
        )

    prop_names = set(prop_binder_names or set())
    if is_standalone_sort_like_lean_expr(rendered):
        return True
    if rendered.startswith("?") or rendered == "_":
        return True

    if _obviously_proposition_like_lean_expr(
        rendered,
        prop_binder_names=prop_names,
        bound_binder_names=bound_binder_names,
    ):
        return False

    if rendered.startswith("¬"):
        negated_body = rendered[1:].strip()
        # Negation is theorem-shaped unless the inner term is itself an
        # obvious non-theorem type expression like `Nat` or `Set α`.
        return _is_non_theorem_standalone_lean_expr_inner(
            negated_body,
            prop_binder_names=prop_names,
            bound_binder_names=bound_binder_names,
        )
    if rendered.lower().startswith("not "):
        negated_body = rendered[4:].strip()
        return _is_non_theorem_standalone_lean_expr_inner(
            negated_body,
            prop_binder_names=prop_names,
            bound_binder_names=bound_binder_names,
        )

    split_arrow = _split_top_level(rendered, "→") or _split_top_level(rendered, "->")
    if split_arrow is not None:
        _left, right = (str(part or "").strip() for part in split_arrow)
        # Arrow goals are non-theorem only when their codomain is itself an
        # obvious non-proposition. Predicate-style codomains like `n ∣ m`
        # should remain admissible even if they lack simple equality/order
        # markers.
        return _is_non_theorem_standalone_lean_expr_inner(
            right,
            prop_binder_names=prop_names,
            bound_binder_names=bound_binder_names,
        )

    head = _head_token_for_non_theorem_check(rendered)
    head_prefix = head.lower().split(".", 1)[0] if head else ""
    if head_prefix in _NON_THEOREM_TYPE_HEADS:
        return True

    if re.fullmatch(_LEAN_QUOTED_IDENTIFIER_PATTERN, rendered):
        return False

    if _LEAN_ATOM_TOKEN_RE.fullmatch(rendered):
        return rendered not in prop_names

    return False


def is_non_theorem_standalone_lean_expr(s: str) -> bool:
    """Return True for standalone non-theorem goals that search should reject."""
    return _is_non_theorem_standalone_lean_expr_inner(
        s,
        prop_binder_names=set(),
    )


# ---------------------------------------------------------------------------
# Lean context-injection helpers
# ---------------------------------------------------------------------------


def is_injectable_lean_type(s: str) -> bool:
    """Heuristic: safe-to-inject Lean type for `lemma name : <type> := ...`.

    This is intentionally more permissive than ``looks_like_lean_type``:
    proven-lemma statements like ``True`` or placeholder identifiers (``A``)
    are valid Lean types but lack strong structural markers.
    """
    s_norm = normalize_statement(str(s or ""))
    if not s_norm:
        return False
    if looks_like_lean_type(s_norm):
        return True
    if s_norm in {"True", "False"}:
        return True
    # Single-token fallback (e.g., `A`, `P`, `Nat`) for test scaffolds and
    # simple Props.  Still rejects obvious prose via the upstream loader/gates.
    return re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", s_norm) is not None


# Keep underscore alias for internal callers (backwards compat)
_looks_like_lean_type = looks_like_lean_type


def _looks_like_extractable_subgoal_type(s: str) -> bool:
    normalized = normalize_statement(str(s or ""))
    unwrapped = normalized
    while True:
        next_unwrapped = _unwrap_single_transparent_parens(unwrapped)
        if next_unwrapped == unwrapped:
            break
        unwrapped = next_unwrapped
    return (
        normalized in {"True", "False"}
        or unwrapped in {"True", "False"}
        or _looks_like_lean_type(normalized)
        or _looks_like_lean_type(unwrapped)
    )


def _has_hard_lowercase_subgoal_label_boundary(raw_statement: str) -> bool:
    text = _rendered_turnstile_target_payload(str(raw_statement or "").strip())
    for _ in range(4):
        first = next((line.strip() for line in text.splitlines() if line.strip()), "")
        if (
            first
            and not first.startswith("SUBGOAL")
            and re.match(r"(?i)^(?:subgoal|goal|target|claim)\s*:", first)
        ):
            return True
        previous = text
        label = re.match(
            r"(?is)^(?:explanation|because|why|note|notes|strategy|proof idea|proof|rationale|reason|comment)\s*:\s*([\s\S]+)$",
            text,
        )
        if label:
            text = label.group(1).strip()
        marker = re.match(r"(?s)^([-*]|\d+[.)])\s+([\s\S]*)$", text)
        if marker:
            text = marker.group(2).strip()
        marker = re.match(r"(?s)^SUBGOAL\s*:\s*([\s\S]+)$", text)
        if marker:
            text = marker.group(1).strip()
        if text == previous:
            break
    return False


_RENDERED_TARGET_CONTINUATION_SUFFIXES = (
    "→",
    "->",
    "=>",
    "↔",
    "<->",
    "∧",
    "∨",
    ",",
    "(",
    "[",
    "{",
    "⦃",
    "+",
    "-",
    "*",
    "/",
    "=",
    "≠",
    "≤",
    "<",
    "≥",
    ">",
    "·",
    "∘",
    "∣",
    "^",
    "%",
    "⊕",
    "⊗",
    "⊔",
    "⊓",
    "∪",
    "∩",
    "∈",
    "∉",
)


def _rendered_target_needs_continuation(text: str) -> bool:
    rhs = str(text or "").strip()
    if not rhs:
        return False
    balance = 0
    pairs = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    closes = {value: key for key, value in pairs.items()}
    for ch in rhs:
        if ch in pairs:
            balance += 1
        elif ch in closes:
            balance = max(0, balance - 1)
    return balance > 0 or rhs.endswith(_RENDERED_TARGET_CONTINUATION_SUFFIXES)


def _has_layout_sensitive_rendered_target(text: str) -> bool:
    for line in str(text or "").splitlines()[:-1]:
        if _line_has_layout_local_let_without_body(line):
            return True
        match = re.search(r"\blet\s+[^;\n]*:=", line)
        if match is None:
            continue
        let_line = line[match.start() :]
        tail = let_line[match.end() - match.start() :]
        if _first_top_level_semicolon(let_line) != -1:
            continue
        if re.search(r"\bin\b", tail):
            continue
        return True
    return False


def _split_rendered_turnstile_goal_blocks(text: str) -> list[str]:
    blocks: list[str] = []
    current: list[str] = []
    lines = str(text or "").splitlines()

    def flush() -> None:
        nonlocal current
        block = "\n".join(current).strip()
        if block and "⊢" in block:
            blocks.append(block)
        current = []

    def context_block_before_next_turnstile(start_idx: int) -> bool:
        for rest in lines[start_idx:]:
            if not rest.strip():
                return False
            if "⊢" in rest:
                return True
            if not _rendered_line_looks_like_goal_context(rest):
                return False
        return False

    for idx, line in enumerate(lines):
        if re.match(r"^\s*case\s+", line) and current:
            flush()
            current.append(line)
            continue
        if (
            current
            and "⊢" not in line
            and any("⊢" in part for part in current)
            and context_block_before_next_turnstile(idx)
        ):
            flush()
            current.append(line)
            continue
        if "⊢" in line and any("⊢" in part for part in current):
            flush()
            current.append(line)
            continue
        if not line.strip():
            next_nonempty = next(
                (rest for rest in lines[idx + 1 :] if rest.strip()),
                "",
            )
            if "⊢" in next_nonempty:
                flush()
                continue
            if any("⊢" in part for part in current) and next_nonempty[:1].isspace():
                current.append(line)
                continue
            if any("⊢" in part for part in current):
                rendered_so_far = "\n".join(current)
                target_so_far = rendered_so_far.split("⊢", 1)[1]
                target_last = next(
                    (
                        item.strip()
                        for item in reversed(target_so_far.splitlines())
                        if item.strip()
                    ),
                    "",
                )
                if (
                    _has_layout_sensitive_rendered_target(target_so_far)
                    or _line_has_layout_local_let_without_body(target_last)
                ):
                    current.append(line)
                    continue
            flush()
            continue
        current.append(line)
    flush()
    return blocks


def _rendered_line_looks_like_goal_context(line: str) -> bool:
    stripped = str(line or "").strip()
    if not stripped or "⊢" in stripped:
        return False
    colon_idx = _first_top_level_colon(stripped)
    if colon_idx <= 0:
        return False
    lhs = stripped[:colon_idx].strip()
    rhs = stripped[colon_idx + 1 :].strip()
    if not lhs or not rhs or ":=" in stripped[: colon_idx + 2]:
        return False
    if _looks_like_subgoal_explanation_line(
        stripped
    ) and not _looks_like_extractable_subgoal_type(rhs):
        return False
    first_lhs_token = lhs.split()[0]
    if first_lhs_token in _BINDER_KEYWORDS or _SUBGOAL_MARKER_INVALID_DECL_HEAD_RE.match(
        first_lhs_token
    ):
        return False
    return all(_LEAN_IDENTIFIER_TOKEN_RE.fullmatch(token) for token in lhs.split())


def _rendered_turnstile_block_target_payload(block: str) -> str:
    target_lines: list[str] = []
    for raw_line in str(block or "").splitlines():
        line = raw_line.strip()
        if not line:
            if target_lines:
                target_lines.append("")
            continue
        if "⊢" in line:
            target_lines = [line.split("⊢", 1)[1].strip()]
            continue
        if target_lines:
            prev = (target_lines[-1] or "").rstrip()
            is_indented = raw_line[:1].isspace()
            target_prefix = "\n".join(target_lines).rstrip()
            target_prefix_last = next(
                (
                    item.strip()
                    for item in reversed(target_prefix.splitlines())
                    if item.strip()
                ),
                "",
            )
            blank_layout_body = bool(
                not prev
                and (
                    _has_layout_sensitive_rendered_target(target_prefix)
                    or _line_has_layout_local_let_without_body(target_prefix_last)
                )
            )
            if (
                _rendered_target_needs_continuation(prev)
                or is_indented
                or blank_layout_body
            ):
                target_lines.append(
                    raw_line.rstrip() if is_indented or not blank_layout_body else "  " + line
                )
                continue
            continue
    target_multiline = "\n".join(item.rstrip() for item in target_lines).strip()
    if "\n" in target_multiline and _has_layout_sensitive_rendered_target(
        target_multiline
    ):
        return target_multiline
    return " ".join(item.strip() for item in target_lines if item).strip()


def _rendered_turnstile_target_payloads(raw_statement: str) -> list[str]:
    text = str(raw_statement or "").strip()
    if "⊢" not in text:
        return []
    blocks = _split_rendered_turnstile_goal_blocks(text) or [text]
    payloads: list[str] = []
    for block in blocks:
        payload = _rendered_turnstile_block_target_payload(block)
        if payload:
            payloads.append(payload)
    return payloads


def _rendered_turnstile_target_payload(raw_statement: str) -> str:
    text = str(raw_statement or "").strip()
    payloads = _rendered_turnstile_target_payloads(text)
    if not payloads:
        return text
    return payloads[0]


def _json_subgoal_statement_payload(raw_statement: str) -> str:
    text = str(raw_statement or "").strip()
    text = _rendered_turnstile_target_payload(text)
    for _ in range(4):
        previous = text
        label = re.match(
            r"(?is)^(?:explanation|because|why|note|notes|strategy|proof idea|proof|rationale|reason|comment)\s*:\s*([\s\S]+)$",
            text,
        )
        if label:
            text = label.group(1).strip()
        marker = re.match(r"(?s)^([-*]|\d+[.)])\s+([\s\S]*)$", text)
        if marker:
            text = marker.group(2).strip()
        marker = re.match(r"(?s)^SUBGOAL\s*:\s*([\s\S]+)$", text)
        if marker:
            text = marker.group(1).strip()
        if text == previous:
            break
    return text


def _subgoal_marker_payload_without_rendered_strip(raw_statement: str) -> str:
    text = str(raw_statement or "").strip()
    for _ in range(4):
        previous = text
        label = re.match(
            r"(?is)^(?:explanation|because|why|note|notes|strategy|proof idea|proof|rationale|reason|comment)\s*:\s*([\s\S]+)$",
            text,
        )
        if label:
            text = label.group(1).strip()
        marker = re.match(r"(?s)^([-*]|\d+[.)])\s+([\s\S]*)$", text)
        if marker:
            text = marker.group(2).strip()
        marker = re.match(r"(?s)^SUBGOAL\s*:\s*([\s\S]+)$", text)
        if marker:
            return marker.group(1).strip()
        if text == previous:
            break
    return ""


def _json_subgoal_statement_shape_payload(raw_statement: str) -> str:
    text = _json_subgoal_statement_payload(raw_statement)
    if _SUBGOAL_DECL_HEAD_RE.match(text):
        colon_idx = _first_top_level_colon(text)
        if colon_idx != -1:
            text = text[colon_idx + 1 :].strip()
            text = _strip_trailing_declaration_proof_assign(text)
    return text


def _json_subgoal_statement_is_proof_fragment(raw_statement: str) -> bool:
    """Reject JSON ``statement`` values that are tactic/proof fragments."""

    payload_text = _json_subgoal_statement_payload(raw_statement)
    proof_assign = r"[\s\S]*:=\s*(?:by\b|rfl\b|trivial\b|exact\b|simp\b|simpa\b)"
    open_proof_assign = r"[\s\S]*:=\s*$"
    if _SUBGOAL_DECL_HEAD_RE.match(payload_text):
        colon_idx = _first_top_level_colon(payload_text)
        if colon_idx != -1:
            declared_type = payload_text[colon_idx + 1 :].strip()
            if re.match(rf"^(?:have|haveI|suffices)\b{proof_assign}", declared_type):
                return True
            if re.match(rf"^(?:let|letI)\b{proof_assign}", declared_type):
                stripped_type = _strip_trailing_declaration_proof_assign(
                    declared_type
                )
                if stripped_type != declared_type:
                    if re.match(r"^(?:have|haveI|suffices)\b", stripped_type):
                        return True
                    if re.match(r"^(?:let|letI)\b", stripped_type) and not (
                        _looks_like_top_level_let_expression(stripped_type)
                        or _layout_local_let_has_body(stripped_type)
                    ):
                        return True
                    return not (
                        not _json_subgoal_statement_is_proof_fragment(stripped_type)
                        and _looks_like_extractable_subgoal_type(stripped_type)
                    )
                if _json_subgoal_statement_is_proof_fragment(declared_type):
                    return True
            if re.match(rf"^(?:have|haveI|let|letI|suffices)\b{open_proof_assign}", declared_type):
                return True
            if re.match(r"^(?:have|haveI|suffices)\b", declared_type):
                return True
            if re.match(r"^(?:let|letI)\b", declared_type) and not (
                _looks_like_top_level_let_expression(declared_type)
                or _layout_local_let_has_body(declared_type)
            ):
                return True
    text = _json_subgoal_statement_shape_payload(raw_statement)
    if _looks_like_orphan_subgoal_proof_line(text):
        return True
    if _looks_like_reasoning_symbolic_prose_fragment(text):
        return True
    has_explicit_top_level_let_body = (
        _first_top_level_semicolon(text) != -1
        or _first_top_level_keyword(text, "in") != -1
    )
    if (
        _line_has_layout_local_let_without_body(text)
        and not _layout_local_let_has_body(text)
        and not has_explicit_top_level_let_body
    ):
        return True
    if (
        "\n" in text
        and _would_leave_incomplete_layout_local_let(text)
        and not has_explicit_top_level_let_body
    ):
        return True
    if re.match(rf"^(?:have|haveI|suffices)\b{proof_assign}", text):
        return True
    if re.match(rf"^(?:have|haveI|let|letI|suffices)\b{open_proof_assign}", text):
        return True
    if re.match(rf"^(?:let|letI)\b{proof_assign}", text):
        if (
            "\n" in text
            and not _layout_local_let_has_body(text)
            and not has_explicit_top_level_let_body
        ):
            return True
        return not _looks_like_top_level_let_expression(text)
    return False


_JSON_KEY_VALUE_RE = re.compile(r'"[A-Za-z_][A-Za-z0-9_]*"\s*:')
_STRUCTURED_DATA_HEADS = (
    "subgoals:",
    "statement:",
    "name:",
    "- subgoals:",
    "- statement:",
    "- name:",
)
_SUBGOAL_EXPLANATION_LABEL_RE = re.compile(
    r"(?i)^(?:explanation|because|why|note|notes|strategy|proof idea|proof|rationale|reason|comment|subgoal)\s*:"
)
_SUBGOAL_EXPLANATION_SENTENCE_RE = re.compile(
    r"(?i)^(?:because|this|thus|hence|therefore|so|we|it|the|a|an|now|then|finally|qed|done)\b"
)
_SUBGOAL_EXPLANATION_SYMBOLIC_SENTENCE_RE = re.compile(
    r"(?i)^(?:this|that|it|which|therefore|hence|thus)\s+"
    r"(?:gives|shows|proves|means|implies|yields|equals|is|are)\b"
)
_SUBGOAL_EXPLANATION_DISCOURSE_PREFIX_RE = re.compile(
    r"(?i)^(?:therefore|hence|thus|so|we\s+have|base\s+case|reflexivity|applying)\b"
)
_SUBGOAL_EXPLANATION_WORDS = frozenset(
    {
        "base",
        "case",
        "cases",
        "claim",
        "clearly",
        "closed",
        "complete",
        "completed",
        "done",
        "follows",
        "finish",
        "finished",
        "goal",
        "holds",
        "immediate",
        "further",
        "needed",
        "no",
        "nothing",
        "obvious",
        "proof",
        "qed",
        "remaining",
        "remains",
        "result",
        "simple",
        "simplification",
        "solved",
        "step",
        "straightforward",
        "target",
        "targets",
        "trivial",
        "work",
        "subgoal",
        "subgoals",
    }
)
_SYMBOLIC_PROSE_VERBS = frozenset(
    {
        "gives",
        "shows",
        "proves",
        "means",
        "implies",
        "reduces",
        "remain",
        "remains",
        "yields",
        "equals",
        "follows",
        "is",
        "are",
    }
)
_LEAN_LINE_MARKERS = "∀∃→↔∧∨¬≤≥⊆∈∉∣:=<>="
_LAYOUT_LOCAL_LET_CONTINUATION_SUFFIXES = (
    ",",
    "→",
    "->",
    "↔",
    "<->",
    "∧",
    "∨",
    "=",
    "≠",
    "≤",
    "≥",
    "<",
    ">",
    ":",
    ":=",
    "+",
    "-",
    "*",
    "/",
    "(",
    "[",
    "{",
)
_TACTIC_PROOF_CONTINUATION_HEADS = (
    "infer_instance",
    "contradiction",
    "constructor",
    "assumption",
    "field_simp",
    "norm_num1",
    "nlinarith",
    "linarith",
    "induction",
    "rewrite",
    "tautology",
    "simp_all",
    "norm_num",
    "suffices",
    "trivial",
    "rintro",
    "refine",
    "decide",
    "cases",
    "exact",
    "intro",
    "intros",
    "simpa",
    "simp",
    "split",
    "subst",
    "tauto",
    "aesop",
    "apply",
    "omega",
    "ring",
    "haveI",
    "have",
    "letI",
    "left",
    "let",
    "right",
    "show",
    "use",
    "rw",
    "rfl",
    "by",
)
_TACTIC_PROOF_CONTINUATION_RE = re.compile(
    r"^(?::=\s*)?(?:"
    + "|".join(re.escape(head) for head in _TACTIC_PROOF_CONTINUATION_HEADS)
    + r")\b"
)
_ORPHAN_SUBGOAL_PROOF_LINE_RE = re.compile(
    r"^(?:"
    + "|".join(
        re.escape(head)
        for head in (
            "done",
            "qed",
            "fun",
            *(
                head
                for head in _TACTIC_PROOF_CONTINUATION_HEADS
                if head not in {"have", "haveI", "let", "letI"}
            ),
        )
    )
    + r")\b"
)


def _looks_like_subgoal_explanation_line(s: str) -> bool:
    """Return True for prose that models append after a formal subgoal."""
    stripped = str(s or "").strip()
    if not stripped:
        return False
    if re.match(r"^SUBGOAL\s*:", stripped):
        return False
    if _SUBGOAL_EXPLANATION_LABEL_RE.match(stripped):
        return True
    if _SUBGOAL_EXPLANATION_DISCOURSE_PREFIX_RE.match(stripped):
        return True
    if _SUBGOAL_EXPLANATION_SYMBOLIC_SENTENCE_RE.match(stripped):
        return True
    if any(sym in stripped for sym in _LEAN_LINE_MARKERS):
        return False
    if not re.search(r"[A-Za-z]", stripped):
        return False
    words = [word.lower() for word in re.findall(r"[A-Za-z]+", stripped)]
    if len(words) >= 2 and any(word in _SUBGOAL_EXPLANATION_WORDS for word in words):
        return True
    if _SUBGOAL_EXPLANATION_SENTENCE_RE.match(stripped) and re.search(r"\s", stripped):
        return True
    if not stripped.endswith((".", "!", "?")):
        return False
    if _SUBGOAL_EXPLANATION_SENTENCE_RE.match(stripped):
        return True
    return bool(re.match(r"^[A-Z][A-Za-z0-9 ,;:'\"()/-]*[.!?]$", stripped))


def _strip_trailing_subgoal_explanation_lines(s: str) -> str:
    raw = str(s or "").strip()
    if "\n" not in raw:
        return raw
    lines = raw.splitlines()
    while len(lines) > 1:
        trailer = lines[-1]
        prefix = "\n".join(lines[:-1]).rstrip()
        if _layout_local_let_trailer_looks_like_symbolic_prose(prefix, trailer):
            if _would_leave_incomplete_layout_local_let(prefix):
                break
            lines.pop()
            continue
        if _layout_local_let_prefix_has_open_rhs(prefix):
            break
        term_continuation = _layout_local_let_trailer_looks_like_term_continuation(
            prefix, trailer
        )
        layout_argument_continuation = (
            _layout_local_let_trailer_looks_like_layout_argument_continuation(
                prefix, trailer
            )
        )
        if term_continuation or layout_argument_continuation:
            break
        if (
            _looks_like_tactic_proof_continuation_line(trailer)
            and _layout_local_let_has_body(prefix)
        ):
            if _would_leave_incomplete_layout_local_let(prefix):
                break
            lines.pop()
            continue
        if _layout_local_let_trailer_looks_like_body(prefix, trailer):
            break
        if _layout_local_let_trailer_looks_like_unscoped_prose_tail(prefix, trailer):
            if _would_leave_incomplete_layout_local_let(prefix):
                break
            lines.pop()
            continue
        if _looks_like_subgoal_explanation_line(trailer):
            if _would_leave_incomplete_layout_local_let(prefix):
                break
            lines.pop()
            continue
        break
    return "\n".join(lines).rstrip()


def _looks_like_tactic_proof_continuation_line(s: str) -> bool:
    stripped = str(s or "").strip()
    return bool(_TACTIC_PROOF_CONTINUATION_RE.match(stripped))


def _layout_local_let_payload(s: str) -> str:
    raw = str(s or "").strip()
    match = re.match(r"(?s)^SUBGOAL\s*:\s*([\s\S]+)$", raw)
    return match.group(1).strip() if match else raw


def _has_unclosed_group(text: str) -> bool:
    depth = 0
    raw = str(text or "")
    i = 0
    while i < len(raw):
        skip_to = _lean_lexical_skip_end(raw, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = raw[i]
        if ch in _GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        i += 1
    return depth > 0


def _layout_local_let_prefix_has_open_rhs(prefix: str) -> bool:
    raw = _layout_local_let_payload(prefix)
    if "let" not in raw:
        return False
    assign_idx = _first_top_level_assign(raw)
    if assign_idx == -1:
        return False
    rhs = raw[assign_idx + 2 :]
    if _has_unclosed_group(rhs):
        return True
    return _line_ends_with_open_proof_tail(raw) and not _layout_local_let_has_body(raw)


def _layout_local_let_binding_name(s: str) -> str:
    raw = _layout_local_let_payload(s)
    if "let" not in raw:
        return ""
    first = next((line for line in raw.splitlines() if "let" in line), "")
    let_idx = first.find("let")
    if let_idx == -1:
        return ""
    match = re.match(
        rf"let\s+({_LEAN_IDENTIFIER_TOKEN_PATTERN}){_LEAN_IDENTIFIER_FOLLOW_PATTERN}",
        first[let_idx:].strip(),
    )
    return match.group(1) if match else ""


def _layout_local_let_names_from_binder_segment(segment: str) -> set[str]:
    raw = str(segment or "").strip()
    names: set[str] = set()

    def add_names(left: str) -> None:
        for token in _LEAN_ATOM_TOKEN_RE.findall(left):
            if token and token not in _BINDER_KEYWORDS:
                names.add(token)

    matched_group = False
    for match in re.finditer(r"[\(\{\[]([^()\[\]{}]+)[\)\}\]]", raw):
        matched_group = True
        content = match.group(1).strip()
        colon_idx = _first_top_level_colon(content)
        if colon_idx >= 0:
            add_names(content[:colon_idx])
    if not matched_group:
        colon_idx = _first_top_level_colon(raw)
        if colon_idx >= 0:
            add_names(raw[:colon_idx])
    return names


def _layout_local_let_bound_names(s: str) -> set[str]:
    raw = _layout_local_let_payload(s)
    names: set[str] = set()
    for match in re.finditer(
        rf"\blet\s+({_LEAN_IDENTIFIER_TOKEN_PATTERN}){_LEAN_IDENTIFIER_FOLLOW_PATTERN}",
        raw,
    ):
        local_name = match.group(1)
        if local_name:
            names.add(local_name)
    binder_raw = raw.lstrip()
    while binder_raw.startswith("(") and binder_raw[1:].lstrip().startswith(
        ("(", "∀", "∃")
    ):
        binder_raw = binder_raw[1:].lstrip()
    binders, _body = _split_leading_forall_statement(binder_raw)
    for binder in binders:
        names.update(_layout_local_let_names_from_binder_segment(binder))
    return names


def _layout_local_let_term_keyword(token: str) -> bool:
    return token in _BINDER_KEYWORDS or token in {
        "by",
        "exact",
        "from",
        "show",
        "if",
        "then",
        "else",
        "match",
        "with",
        "fun",
        "True",
        "False",
        "Prop",
        "Type",
        "Sort",
    }


def _layout_local_let_lower_term_constant(token: str) -> bool:
    return token in {"some", "none", "id", "true", "false", "default", "rfl", "trivial"}


def _layout_local_let_lower_token_looks_like_prose(token: str) -> bool:
    return token in _SUBGOAL_EXPLANATION_WORDS or token in {
        "because",
        "check",
        "consider",
        "counter",
        "deduce",
        "example",
        "finish",
        "finite",
        "from",
        "inspect",
        "now",
        "observe",
        "sanity",
        "small",
        "there",
        "therefore",
        "these",
        "this",
        "those",
        "thus",
        "that",
        "test",
        "we",
        "which",
    } or token in _SYMBOLIC_PROSE_VERBS


def _layout_local_let_token_is_scoped_term_part(
    token: str, bound_names: set[str], *, allow_lower_term_head: bool = False
) -> bool:
    if not token:
        return False
    if _layout_local_let_term_keyword(token):
        return True
    if _layout_local_let_lower_term_constant(token):
        return True
    if token in bound_names:
        return True
    if "." not in token:
        return bool(
            allow_lower_term_head
            and token[:1].islower()
            and not _layout_local_let_lower_token_looks_like_prose(token)
        )
    base = token.split(".", 1)[0]
    return base in bound_names or bool(base and base[0].isupper())


def _layout_local_let_tokens_are_scoped_term(
    text: str, bound_names: set[str]
) -> bool:
    rendered = str(text or "")
    tokens = _LEAN_ATOM_TOKEN_RE.findall(rendered)
    if not tokens:
        return False
    meaningful = [tok for tok in tokens if not _layout_local_let_term_keyword(tok)]
    if not meaningful:
        return False
    parenthesized_term = "(" in rendered and ")" in rendered
    evidence_after_head = any(
        _layout_local_let_token_is_scoped_term_part(
            tok, bound_names, allow_lower_term_head=False
        )
        for tok in meaningful[1:]
    )
    allow_lower_term_head = parenthesized_term and evidence_after_head
    return all(
        _layout_local_let_token_is_scoped_term_part(
            tok, bound_names, allow_lower_term_head=allow_lower_term_head
        )
        for tok in meaningful
    )


def _layout_local_let_trailer_looks_like_bound_application(
    prefix: str, trailer: str
) -> bool:
    stripped = str(trailer or "").strip()
    if not stripped or stripped.endswith((".", "!", "?")):
        return False
    bound_names = _layout_local_let_bound_names(prefix)
    if not bound_names:
        return False
    tokens = _LEAN_ATOM_TOKEN_RE.findall(stripped)
    if not tokens or tokens[0] not in bound_names:
        return False
    if all(
        _layout_local_let_token_is_scoped_term_part(
            token,
            bound_names,
            allow_lower_term_head=True,
        )
        for token in tokens[1:]
    ):
        return True
    return _layout_local_let_tokens_are_scoped_term(stripped, bound_names)


def _layout_local_let_trailer_looks_like_show_body(
    prefix: str, trailer: str
) -> bool:
    stripped = str(trailer or "").strip()
    if not stripped.startswith("show ") or stripped.endswith((".", "!", "?")):
        return False
    bound_names = _layout_local_let_bound_names(prefix)
    if not bound_names:
        return False
    match = re.search(r"\bfrom\b([\s\S]+)$", stripped)
    if match is None:
        return False
    term = match.group(1).strip()
    if not _layout_local_let_tokens_are_scoped_term(term, bound_names):
        return False
    term_tokens = [
        tok
        for tok in _LEAN_ATOM_TOKEN_RE.findall(term)
        if not _layout_local_let_term_keyword(tok)
    ]
    return any(
        tok in bound_names or (("." in tok) and tok.split(".", 1)[0] in bound_names)
        for tok in term_tokens
    )


def _layout_local_let_trailer_looks_like_scoped_term(prefix: str, trailer: str) -> bool:
    return _layout_local_let_trailer_looks_like_bound_application(
        prefix, trailer
    ) or _layout_local_let_trailer_looks_like_show_body(prefix, trailer)


def _layout_local_let_prefix_expects_term_continuation(prefix: str) -> bool:
    raw = _layout_local_let_payload(prefix)
    lines = [line.strip() for line in raw.splitlines() if line.strip()]
    if not lines:
        return False
    last = lines[-1]
    if last.endswith(_LAYOUT_LOCAL_LET_CONTINUATION_SUFFIXES):
        return True
    return _has_unclosed_group(last)


def _line_indent_width(line: str) -> int:
    raw = str(line or "")
    return len(raw) - len(raw.lstrip(" \t"))


def _layout_local_let_trailer_looks_like_layout_argument_continuation(
    prefix: str, trailer: str
) -> bool:
    if not _layout_local_let_has_body(prefix):
        return False
    raw_trailer = str(trailer or "")
    if not raw_trailer.strip() or raw_trailer.lstrip(" \t") == raw_trailer:
        return False
    prefix_lines = [
        line for line in _layout_local_let_payload(prefix).splitlines() if line.strip()
    ]
    if not prefix_lines:
        return False
    previous_line = prefix_lines[-1]
    if _line_indent_width(raw_trailer) <= _line_indent_width(previous_line):
        return False
    previous = previous_line.strip()
    if not _layout_local_let_trailer_looks_like_bound_application(prefix, previous):
        return False
    stripped = raw_trailer.strip()
    if _layout_local_let_trailer_looks_like_symbolic_prose(prefix, stripped):
        return False
    if _looks_like_tactic_proof_continuation_line(stripped):
        return False
    tokens = _LEAN_ATOM_TOKEN_RE.findall(stripped)
    if not tokens:
        return False
    bound_names = _layout_local_let_bound_names(prefix)
    if not bound_names:
        return False
    if _layout_local_let_lower_token_looks_like_prose(tokens[0].lower()):
        return False
    return all(
        _layout_local_let_token_is_scoped_term_part(
            token,
            bound_names,
            allow_lower_term_head=True,
        )
        for token in tokens
    )


def _layout_local_let_trailer_looks_like_term_continuation(
    prefix: str, trailer: str
) -> bool:
    if not _layout_local_let_has_body(prefix):
        return False
    if not _layout_local_let_prefix_expects_term_continuation(prefix):
        return False
    stripped = str(trailer or "").strip()
    if not stripped:
        return False
    if _layout_local_let_trailer_looks_like_symbolic_prose(prefix, stripped):
        return False
    if _layout_local_let_trailer_looks_like_scoped_term(prefix, stripped):
        return True
    if _looks_like_subgoal_explanation_line(stripped):
        return False
    if _looks_like_tactic_proof_continuation_line(
        stripped
    ) and not _layout_local_let_trailer_looks_like_show_body(prefix, stripped):
        return False
    bound_names = _layout_local_let_bound_names(prefix)
    if not bound_names:
        return False
    tokens = _LEAN_ATOM_TOKEN_RE.findall(stripped)
    if not tokens:
        return False
    if _layout_local_let_lower_token_looks_like_prose(tokens[0].lower()):
        return False
    has_bound_evidence = any(
        token in bound_names
        or ("." in token and token.split(".", 1)[0] in bound_names)
        for token in tokens
    )
    if not has_bound_evidence:
        return False
    return any(sym in stripped for sym in _LEAN_LINE_MARKERS)


def _layout_local_let_trailer_looks_like_symbolic_prose(
    prefix: str, trailer: str
) -> bool:
    stripped = str(trailer or "").strip()
    bound_names = _layout_local_let_bound_names(prefix)
    if not stripped or not bound_names:
        return False
    label_match = re.match(r"^([A-Za-z_][A-Za-z0-9_']*):\s+", stripped)
    if label_match is not None:
        head = label_match.group(1)
        return head in bound_names or _layout_local_let_lower_token_looks_like_prose(
            head.lower()
        )
    tokens = _LEAN_ATOM_TOKEN_RE.findall(stripped)
    if len(tokens) < 2 or tokens[0] not in bound_names:
        return bool(
            len(tokens) >= 2
            and _layout_local_let_lower_token_looks_like_prose(tokens[0].lower())
            and tokens[1].lower() in _SYMBOLIC_PROSE_VERBS
        )
    verb = tokens[1].lower()
    return verb in _SYMBOLIC_PROSE_VERBS and tokens[1] not in bound_names


def _layout_local_let_trailer_looks_like_unscoped_prose_tail(
    prefix: str, trailer: str
) -> bool:
    if not _layout_local_let_has_body(prefix):
        return False
    stripped = str(trailer or "").strip()
    if not stripped:
        return False
    inner = stripped
    if inner.startswith("(") and inner.endswith(")"):
        inner = inner[1:-1].strip()
    tokens = _LEAN_ATOM_TOKEN_RE.findall(inner)
    if not tokens:
        return False
    head = tokens[0]
    bound_names = _layout_local_let_bound_names(prefix)
    if head in bound_names:
        return True
    if _layout_local_let_token_is_scoped_term_part(
        head, bound_names, allow_lower_term_head=False
    ):
        return False
    if _layout_local_let_lower_token_looks_like_prose(head.lower()):
        return True
    return bool(head[:1].islower())


def _layout_local_let_trailer_looks_like_body(prefix: str, trailer: str) -> bool:
    stripped = str(trailer or "").strip()
    bound_names = _layout_local_let_bound_names(prefix)
    local_names = {
        match.group(1)
        for match in re.finditer(
            rf"\blet\s+({_LEAN_IDENTIFIER_TOKEN_PATTERN}){_LEAN_IDENTIFIER_FOLLOW_PATTERN}",
            _layout_local_let_payload(prefix),
        )
    }
    if not local_names or not stripped:
        return False
    if _layout_local_let_trailer_looks_like_symbolic_prose(prefix, stripped):
        return False
    if _looks_like_reasoning_symbolic_prose_fragment(stripped):
        return False
    tokens = _LEAN_ATOM_TOKEN_RE.findall(stripped)
    if tokens and tokens[0] in local_names:
        if all(
            _layout_local_let_token_is_scoped_term_part(
                token,
                bound_names,
                allow_lower_term_head=True,
            )
            for token in tokens[1:]
        ):
            return True
        if _layout_local_let_tokens_are_scoped_term(stripped, bound_names):
            return True
        if len(tokens) >= 2 and all(
            _LEAN_ATOM_TOKEN_RE.fullmatch(token) for token in tokens[1:]
        ):
            return True
        return any(sym in stripped for sym in _LEAN_LINE_MARKERS)
    return _layout_local_let_trailer_looks_like_scoped_term(prefix, stripped)


def _layout_local_let_trailer_looks_like_lean_application(trailer: str) -> bool:
    stripped = str(trailer or "").strip()
    if not stripped or stripped.endswith((".", "!", "?")):
        return False
    tokens = _LEAN_ATOM_TOKEN_RE.findall(stripped)
    if len(tokens) < 2 or len(" ".join(tokens)) != len(stripped):
        return False
    if tokens[1].lower() in _SYMBOLIC_PROSE_VERBS:
        return False
    if _layout_local_let_lower_token_looks_like_prose(tokens[0].lower()) and tokens[
        0
    ] not in {"goal", "claim", "target", "subgoal"}:
        return False
    return all(token not in _BINDER_KEYWORDS for token in tokens)


def _layout_local_let_rhs_starts_tactic_proof(rhs: str) -> bool:
    stripped = str(rhs or "").lstrip()
    while stripped.startswith("("):
        stripped = stripped[1:].lstrip()
    return stripped.startswith("by")


def _layout_local_let_has_body(s: str) -> bool:
    raw = str(s or "").strip()
    if "\n" not in raw or "let" not in raw:
        return False
    lines = raw.splitlines()
    first_idx = next((idx for idx, line in enumerate(lines) if "let" in line), -1)
    if first_idx == -1:
        return False
    first = lines[first_idx]
    let_idx = first.find("let")
    candidate = first[let_idx:].strip()
    assign_idx = _first_top_level_assign(candidate)
    if assign_idx == -1:
        return False
    rhs = candidate[assign_idx + 2 :].strip()
    tail_lines = [line.strip() for line in lines[first_idx + 1 :] if line.strip()]
    if not tail_lines:
        return False
    if not _layout_local_let_rhs_starts_tactic_proof(rhs):
        rhs_prefix = "\n".join(lines[: first_idx + 1])
        rhs_lines = [rhs]
        for line in tail_lines:
            previous = rhs_lines[-1] if rhs_lines else rhs
            if (
                _layout_local_let_prefix_expects_term_continuation(previous)
                or _line_ends_with_open_proof_tail(previous)
            ):
                rhs_lines.append(line)
                continue
            if re.match(r"^let\s+[A-Za-z_][A-Za-z0-9_']*\b", line):
                return True
            if _layout_local_let_trailer_looks_like_symbolic_prose(rhs_prefix, line):
                continue
            if _looks_like_reasoning_symbolic_prose_fragment(line):
                continue
            if _layout_local_let_trailer_looks_like_body(rhs_prefix, line):
                return True
            if _layout_local_let_trailer_looks_like_lean_application(line):
                return True
            if _looks_like_subgoal_explanation_line(line):
                continue
            if _looks_like_tactic_proof_continuation_line(line):
                continue
            return True
        return False
    for line in tail_lines:
        if _layout_local_let_trailer_looks_like_symbolic_prose(
            "\n".join(lines[: first_idx + 1]), line
        ):
            continue
        if _looks_like_reasoning_symbolic_prose_fragment(line):
            continue
        if _layout_local_let_trailer_looks_like_body("\n".join(lines[: first_idx + 1]), line):
            return True
        if _layout_local_let_trailer_looks_like_lean_application(line):
            return True
        if _looks_like_subgoal_explanation_line(line):
            continue
        if _looks_like_tactic_proof_continuation_line(line):
            continue
        return True
    return False


def _would_leave_incomplete_layout_local_let(prefix: str) -> bool:
    raw = str(prefix or "").strip()
    if not raw:
        return False
    return any(
        _line_has_layout_local_let_without_body(line.strip())
        for line in raw.splitlines()
        if line.strip()
    ) and not _layout_local_let_has_body(raw)


def _looks_like_orphan_subgoal_proof_line(s: str) -> bool:
    """Reject proof-term/tactic continuation lines emitted after SUBGOAL rows."""
    stripped = str(s or "").strip()
    return bool(_ORPHAN_SUBGOAL_PROOF_LINE_RE.match(stripped))


def _line_ends_with_open_proof_tail(s: str) -> bool:
    stripped = str(s or "").rstrip()
    return bool(re.search(r"(?:^|[\s(])by\s*$", stripped))


def _looks_like_serialized_data_line(s: str) -> bool:
    """Heuristic guard: reject JSON/YAML-ish lines in Lean subgoal extraction."""
    if not s:
        return False
    t = s.strip()
    if not t:
        return False
    lower = t.lower()
    if lower.startswith(_STRUCTURED_DATA_HEADS):
        return True
    if _JSON_KEY_VALUE_RE.search(t):
        return True
    if t[0] in "{[":
        try:
            parsed = json.loads(t)
        except Exception:
            # Likely a serialized-object fragment (e.g. truncated JSON).
            if '"' in t and ":" in t and any(ch in t for ch in "{}[]"):
                return True
            return False
        return isinstance(parsed, (dict, list))
    return False


def _extract_subgoals_from_json_payload(data: object) -> list[str]:
    """Extract formal subgoal statements from parsed JSON payloads."""
    extracted: list[str] = []
    hard_rejected = False

    def append_candidate(raw_statement: str) -> None:
        nonlocal hard_rejected
        if _has_hard_lowercase_subgoal_label_boundary(raw_statement):
            hard_rejected = True
            extracted.clear()
            return
        if re.search(r"\bSUBGOAL\s*:", raw_statement):
            nested = extract_subgoal_statements(raw_statement)
            if nested:
                extracted.extend(nested)
            return
        rendered = _extract_rendered_turnstile_subgoal_statements(raw_statement)
        if rendered:
            extracted.extend(rendered)
            return
        if _json_subgoal_statement_is_proof_fragment(raw_statement):
            return
        stmt = normalize_subgoal_statement(
            _json_subgoal_statement_payload(raw_statement)
        )
        if (
            not _json_subgoal_statement_is_proof_fragment(stmt)
            and _looks_like_extractable_subgoal_type(stmt)
        ):
            extracted.append(stmt)

    if isinstance(data, dict):
        raw_subgoals = data.get("subgoals", [])
        if isinstance(raw_subgoals, list):
            for sg in raw_subgoals:
                if isinstance(sg, dict) and isinstance(sg.get("statement"), str):
                    append_candidate(sg["statement"])
                elif isinstance(sg, str):
                    append_candidate(sg)
                if hard_rejected:
                    return []
    elif isinstance(data, list):
        for sg in data:
            if isinstance(sg, str):
                append_candidate(sg)
            elif isinstance(sg, dict) and isinstance(sg.get("statement"), str):
                append_candidate(sg["statement"])
            if hard_rejected:
                return []
    return extracted


def _first_top_level_comma(s: str) -> int:
    """Return index of the first top-level comma (depth 0), or -1."""
    depth = 0
    i = 0
    while i < len(s):
        skip_to = _lean_lexical_skip_end(s, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = s[i]
        if ch in _GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == "," and depth == 0:
            return i
        i += 1
    return -1


def _first_top_level_colon(s: str) -> int:
    """Return index of the first top-level ':' (excluding ':='), or -1."""
    depth = 0
    i = 0
    while i < len(s):
        skip_to = _lean_lexical_skip_end(s, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = s[i]
        if ch in _GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == ":" and depth == 0:
            if i + 1 < len(s) and s[i + 1] == "=":
                i += 1
                continue
            return i
        i += 1
    return -1


def _lean_lexical_skip_end(text: str, idx: int) -> Optional[int]:
    """Return the exclusive end of a Lean lexical atom beginning at *idx*."""

    raw = str(text or "")
    if idx < 0 or idx >= len(raw):
        return None
    opener = raw[idx]
    if opener not in {"r", "«", '"', "'", "/", "-"}:
        return None
    if opener == "r":
        hash_idx = idx + 1
        while hash_idx < len(raw) and raw[hash_idx] == "#":
            hash_idx += 1
        if hash_idx < len(raw) and raw[hash_idx] == '"':
            terminator = '"' + raw[idx + 1 : hash_idx]
            end = raw.find(terminator, hash_idx + 1)
            return len(raw) if end == -1 else end + len(terminator)
    if raw.startswith("«", idx):
        end = raw.find("»", idx + 1)
        return len(raw) if end == -1 else end + 1
    if opener == '"':
        i = idx + 1
        escaped = False
        while i < len(raw):
            ch = raw[i]
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                return i + 1
            i += 1
        return len(raw)
    if opener == "'":
        previous = raw[idx - 1] if idx > 0 else ""
        if not (previous.isalnum() or (bool(previous) and previous in "_'»")):
            i = idx + 1
            escaped = False
            while i < len(raw):
                ch = raw[i]
                if escaped:
                    escaped = False
                elif ch == "\\":
                    escaped = True
                elif ch == "'":
                    return i + 1
                i += 1
    if raw.startswith("/-", idx):
        depth = 1
        i = idx + 2
        while i < len(raw):
            if raw.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if raw.startswith("-/", i):
                depth -= 1
                i += 2
                if depth == 0:
                    return i
                continue
            i += 1
        return len(raw)
    if raw.startswith("--", idx):
        end = raw.find("\n", idx + 2)
        return len(raw) if end == -1 else end
    return None


def _lean_qualified_identifier_segments(name: str) -> tuple[str, ...]:
    """Split a Lean name on qualification dots, preserving quoted segments."""

    raw = str(name or "").strip()
    if not raw:
        return ()
    segments: List[str] = []
    start = 0
    quoted = False
    for index, char in enumerate(raw):
        if char == "«" and not quoted:
            quoted = True
        elif char == "»" and quoted:
            quoted = False
        elif char == "." and not quoted:
            segment = raw[start:index]
            if not segment:
                return ()
            segments.append(segment)
            start = index + 1
    final = raw[start:]
    if not final or quoted:
        return ()
    segments.append(final)
    return tuple(segments)


def canonical_lean_identifier(name: str) -> str:
    """Return a comparison key for Lean-equivalent identifier spellings."""

    segments = _lean_qualified_identifier_segments(name)
    if not segments:
        return str(name or "").strip()
    normalized: List[str] = []
    for segment in segments:
        if segment.startswith("«") and segment.endswith("»"):
            inner = segment[1:-1]
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", inner):
                segment = inner
        normalized.append(segment)
    return ".".join(normalized)


def rename_lean_identifier(
    source: str,
    old_name: str,
    new_name: str,
    *,
    allow_arbitrary_dot_suffixes: bool = False,
) -> str:
    """Rename references to one Lean declaration without touching lexical data."""

    raw = str(source or "")
    old = str(old_name or "").strip()
    new = str(new_name or "").strip()
    if not old or old == new:
        return raw
    old_segments = _lean_qualified_identifier_segments(old)
    new_segments = _lean_qualified_identifier_segments(new)
    old_short = old_segments[-1] if old_segments else old
    new_short = new_segments[-1] if new_segments else new
    allow_short_reference = len(old_segments) > 1
    projection_suffixes = frozenset(
        {
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
    )

    identifier_pattern = r"(?:«[^»]+»|[A-Za-z_][A-Za-z0-9_']*)"
    declaration_match = re.search(
        rf"\b(?:theorem|lemma|def|abbrev|opaque|instance)\s+"
        rf"(?P<name>{identifier_pattern}(?:\.{identifier_pattern})*)",
        raw,
    )
    declaration_name_span: tuple[int, int] | None = None
    declaration_parameter_names: set[str] = set()
    if declaration_match is not None:
        declaration_name_span = declaration_match.span("name")
        header_end = raw.find(":=", declaration_match.end("name"))
        if header_end < 0:
            header_end = len(raw)
        header = raw[declaration_match.end("name") : header_end]
        for binder in re.finditer(r"[({\[]([^(){}\[\]]+)[)}\]]", header):
            binder_body = str(binder.group(1) or "")
            if ":" not in binder_body:
                continue
            lhs = binder_body.split(":", 1)[0]
            for parameter_name in re.findall(identifier_pattern, lhs):
                canonical = canonical_lean_identifier(parameter_name)
                if canonical and canonical != "_":
                    declaration_parameter_names.add(canonical)
    old_short_is_shadowed = (
        len(old_segments) == 1
        and canonical_lean_identifier(old_short) in declaration_parameter_names
    )

    def identifier_end(start: int) -> Optional[int]:
        def segment_end(index: int) -> Optional[int]:
            if index >= len(raw):
                return None
            if raw.startswith("«", index):
                end = raw.find("»", index + 1)
                return len(raw) if end < 0 else end + 1
            if not (raw[index].isalpha() or raw[index] == "_"):
                return None
            end = index + 1
            while end < len(raw) and (
                raw[end].isalnum() or raw[end] in "_'"
            ):
                end += 1
            return end

        end = segment_end(start)
        if end is None:
            return None
        while end < len(raw) and raw[end] == ".":
            next_end = segment_end(end + 1)
            if next_end is None:
                break
            end = next_end
        return end

    def renamed_token(token: str, token_start: int) -> str:
        token_segments = _lean_qualified_identifier_segments(token)
        if not token_segments:
            return token
        token_keys = tuple(canonical_lean_identifier(item) for item in token_segments)
        old_keys = tuple(canonical_lean_identifier(item) for item in old_segments)
        short_key = canonical_lean_identifier(old_short)
        rooted = bool(token_keys and token_keys[0] == "_root_")
        comparison_keys = token_keys[1:] if rooted else token_keys
        comparison_segments = token_segments[1:] if rooted else token_segments
        is_declaration_name = bool(
            declaration_name_span is not None
            and token_start == declaration_name_span[0]
            and token_start + len(token) == declaration_name_span[1]
        )

        def replacement(
            prefix_length: int,
            replacement_segments: tuple[str, ...],
        ) -> str:
            prefix = ("_root_",) if rooted else ()
            suffix = comparison_segments[prefix_length:]
            return ".".join((*prefix, *replacement_segments, *suffix))

        if comparison_keys == old_keys:
            if old_short_is_shadowed and not is_declaration_name:
                return token
            return replacement(len(old_keys), new_segments)
        if comparison_keys[: len(old_keys)] == old_keys and len(
            comparison_keys
        ) > len(old_keys):
            suffix = comparison_keys[len(old_keys)]
            if (
                len(old_segments) > 1
                or allow_arbitrary_dot_suffixes
                or suffix in projection_suffixes
            ):
                return replacement(len(old_keys), new_segments)
        if allow_short_reference:
            if comparison_keys == (short_key,):
                return replacement(1, (new_short,))
            if comparison_keys[:1] == (short_key,) and len(comparison_keys) > 1:
                suffix = comparison_keys[1]
                if allow_arbitrary_dot_suffixes or suffix in projection_suffixes:
                    return replacement(1, (new_short,))
        return token

    out: List[str] = []
    index = 0
    while index < len(raw):
        skip_to = _lean_lexical_skip_end(raw, index)
        if skip_to is not None and not raw.startswith("«", index):
            out.append(raw[index:skip_to])
            index = skip_to
            continue
        end = identifier_end(index)
        if end is not None:
            token = raw[index:end]
            out.append(renamed_token(token, index))
            index = end
            continue
        out.append(raw[index])
        index += 1
    return "".join(out)


def fresh_lean_alternative_identifier(
    name: str,
    reserved_names: Sequence[str],
) -> str:
    """Return a deterministic valid Lean name for a colliding declaration."""

    original = str(name or "").strip()
    reserved = {
        canonical_lean_identifier(str(item or "").strip())
        for item in reserved_names
    }
    quoted_segment_start = original.rfind("«")
    quoted = quoted_segment_start >= 0 and original.endswith("»")
    prefix = original[:quoted_segment_start] if quoted else ""
    stem = original[quoted_segment_start + 1 : -1] if quoted else original

    def candidate_for(suffix: str) -> str:
        candidate = f"{stem}_alternative{suffix}"
        return f"{prefix}«{candidate}»" if quoted else candidate

    candidate = candidate_for("")
    ordinal = 2
    while canonical_lean_identifier(candidate) in reserved:
        candidate = candidate_for(f"_{ordinal}")
        ordinal += 1
    return candidate


def _first_top_level_assign(s: str) -> int:
    """Return index of the first top-level ':=', or -1."""
    depth = 0
    i = 0
    while i < len(s) - 1:
        skip_to = _lean_lexical_skip_end(s, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = s[i]
        if ch in _GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == ":" and s[i + 1] == "=" and depth == 0:
            return i
        i += 1
    return -1


def _top_level_assign_positions(s: str) -> list[int]:
    """Return all top-level ':=' positions."""
    positions: list[int] = []
    depth = 0
    i = 0
    while i < len(s) - 1:
        skip_to = _lean_lexical_skip_end(s, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = s[i]
        if ch in _GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == ":" and s[i + 1] == "=" and depth == 0:
            positions.append(i)
            i += 1
        i += 1
    return positions


def _top_level_semicolon_positions(s: str) -> list[int]:
    """Return all top-level semicolon positions."""
    positions: list[int] = []
    depth = 0
    i = 0
    while i < len(s):
        skip_to = _lean_lexical_skip_end(s, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = s[i]
        if ch in _GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == ";" and depth == 0:
            positions.append(i)
        i += 1
    return positions


def _looks_like_declaration_proof_tail(s: str) -> bool:
    tail = str(s or "").strip()
    if not tail:
        return False
    while True:
        unwrapped = _unwrap_single_transparent_parens(tail)
        if unwrapped == tail:
            break
        tail = unwrapped.strip()
    if re.match(r"^by(?:\s|$)", tail):
        return True
    return tail.startswith(
        (
            "sorry",
            "rfl",
            "exact ",
            "have ",
            "haveI ",
            "let ",
            "letI ",
            "suffices ",
            "simpa",
            "simp",
            "omega",
            "linarith",
            "nlinarith",
            "aesop",
        )
    )


def _assign_is_local_let_binding(raw: str, idx: int) -> bool:
    """Return True when the top-level ``:=`` at *idx* is a local-let binder."""
    text = str(raw or "")
    if idx < 0:
        return False
    segment_start = 0
    _binders, body = _split_leading_forall_statement(text)
    body_start = text.rfind(body) if body else -1
    if body_start != -1:
        implication_prefix, conclusion = _split_top_level_implication_conclusion(
            body
        )
        if conclusion.startswith("let "):
            segment_start = body_start + len(implication_prefix)
    for semicolon_idx in _top_level_semicolon_positions(text):
        if segment_start <= semicolon_idx < idx:
            segment_start = semicolon_idx + 1
    segment = text[segment_start:]
    segment_stripped = segment.lstrip()
    segment_offset = segment_start + (len(segment) - len(segment_stripped))
    if not segment_stripped.startswith("let "):
        return False
    segment_assign = _first_top_level_assign(segment_stripped)
    return segment_assign != -1 and idx == segment_offset + segment_assign


def _assign_is_tactic_local_binding(raw: str, idx: int) -> bool:
    """Return True for tactic-local bindings like ``have h := by ...``."""
    text = str(raw or "")
    if idx < 0:
        return False
    line_start = text.rfind("\n", 0, idx) + 1
    semicolon_start = text.rfind(";", 0, idx) + 1
    assign_start = text.rfind(":=", 0, idx) + 2
    segment_start = max(line_start, semicolon_start, assign_start)
    lhs = text[segment_start:idx].strip()
    if not lhs and line_start > 0:
        prev_line_end = line_start - 1
        prev_line_start = text.rfind("\n", 0, prev_line_end) + 1
        lhs = text[prev_line_start:prev_line_end].strip()
    if lhs.startswith("by "):
        lhs = lhs[3:].lstrip()
    return bool(re.match(r"^(?:haveI|letI|have|let|suffices)\b", lhs))


def _strip_trailing_declaration_proof_assign(s: str) -> str:
    raw = str(s or "").strip()
    for idx in _top_level_assign_positions(raw):
        if _assign_is_local_let_binding(raw, idx) or _assign_is_tactic_local_binding(raw, idx):
            continue
        rhs = raw[idx + 2 :].strip()
        if _looks_like_declaration_proof_tail(rhs):
            return raw[:idx].rstrip()
    return raw


def _first_top_level_semicolon(s: str) -> int:
    """Return index of the first top-level ';', or -1."""
    depth = 0
    i = 0
    while i < len(s):
        skip_to = _lean_lexical_skip_end(s, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = s[i]
        if ch in _GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == ";" and depth == 0:
            return i
        i += 1
    return -1


def _first_top_level_keyword(s: str, keyword: str) -> int:
    """Return the first top-level keyword token index, or -1."""
    token = str(keyword or "").strip()
    if not token:
        return -1
    depth = 0
    idx = 0
    while idx < len(s):
        skip_to = _lean_lexical_skip_end(s, idx)
        if skip_to is not None:
            idx = skip_to
            continue
        ch = s[idx]
        if ch in _GROUP_OPEN_TO_CLOSE:
            depth += 1
            idx += 1
            continue
        if ch in _GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
            idx += 1
            continue
        if depth == 0 and s.startswith(token, idx):
            before_ok = idx == 0 or s[idx - 1].isspace()
            after_idx = idx + len(token)
            after_ok = after_idx >= len(s) or s[after_idx].isspace()
            if before_ok and after_ok:
                return idx
        idx += 1
    return -1


def _looks_like_top_level_let_expression(s: str) -> bool:
    raw = str(s or "").strip()
    if not raw.startswith("let"):
        return False
    assign_idx = _first_top_level_assign(raw)
    if assign_idx == -1:
        return False
    tail = raw[assign_idx + 2 :]
    return (
        _first_top_level_semicolon(raw) != -1
        or _first_top_level_keyword(raw, "in") != -1
        or "\n" in tail
    )


_TOP_LEVEL_BINDER_IN_OPERATORS = (
    "∀ᶠ",
    "∃ᶠ",
    "∑",
    "∏",
    "∫",
    "⨍",
    "⋃",
    "⋂",
    "⨆",
    "⨅",
    "∐",
)


def _is_top_level_binder_operator_in(
    text: str,
    *,
    start: int,
    in_idx: int,
) -> bool:
    """Whether ``in`` belongs to a top-level binder operator, not a let."""

    last_operator = -1
    last_comma = -1
    depth = 0
    i = max(0, int(start or 0))
    stop = min(len(text), max(i, int(in_idx or 0)))
    while i < stop:
        skip_to = _lean_lexical_skip_end(text, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = text[i]
        if ch in _GROUP_OPEN_TO_CLOSE:
            depth += 1
            i += 1
            continue
        if ch in _GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
            i += 1
            continue
        if depth == 0:
            matched = next(
                (
                    token
                    for token in _TOP_LEVEL_BINDER_IN_OPERATORS
                    if text.startswith(token, i)
                ),
                None,
            )
            if matched is not None:
                last_operator = i
                i += len(matched)
                continue
            if ch == ",":
                last_comma = i
        i += 1
    return last_operator > last_comma


def _top_level_local_let_body_in_index(text: str, *, assign_idx: int) -> int:
    """Locate the ``in`` closing one local let, skipping nested binders."""

    raw = str(text or "")
    nested_lets = 0
    i = max(0, int(assign_idx or 0) + 2)
    while i < len(raw):
        skip_to = _lean_lexical_skip_end(raw, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = raw[i]
        if ch in _GROUP_OPEN_TO_CLOSE:
            group_end = _scan_group(raw, i)
            i = group_end if group_end is not None else i + 1
            continue
        for keyword in ("let", "in"):
            if not raw.startswith(keyword, i):
                continue
            before_ok = i == 0 or not _is_lean_identifier_continue_char(raw[i - 1])
            after = i + len(keyword)
            after_ok = after >= len(raw) or not _is_lean_identifier_continue_char(
                raw[after]
            )
            if not (before_ok and after_ok):
                continue
            if keyword == "let":
                nested_lets += 1
            elif _is_top_level_binder_operator_in(
                raw,
                start=assign_idx + 2,
                in_idx=i,
            ):
                pass
            elif nested_lets > 0:
                nested_lets -= 1
            else:
                return i
            i = after
            break
        else:
            i += 1
    return -1


def _line_has_layout_local_let_without_body(line: str) -> bool:
    raw = str(line or "")
    start = 0
    while True:
        idx = raw.find("let", start)
        if idx < 0:
            return False
        before = raw[idx - 1] if idx > 0 else " "
        after_idx = idx + len("let")
        after = raw[after_idx] if after_idx < len(raw) else " "
        if (before.isalnum() or before == "_") or (after.isalnum() or after == "_"):
            start = idx + len("let")
            continue
        candidate = raw[idx:].strip()
        assign_idx = _first_top_level_assign(candidate)
        if assign_idx == -1:
            start = idx + len("let")
            continue
        has_let_body_in = False
        search_start = assign_idx + 2
        while search_start < len(candidate):
            suffix_in_idx = _first_top_level_keyword(candidate[search_start:], "in")
            if suffix_in_idx == -1:
                break
            in_idx = search_start + suffix_in_idx
            if not _is_top_level_binder_operator_in(
                candidate,
                start=assign_idx + 2,
                in_idx=in_idx,
            ):
                has_let_body_in = True
                break
            search_start = in_idx + len("in")
        semicolon_idx = _first_top_level_semicolon(candidate)
        rhs = candidate[assign_idx + 2 :].strip()
        semicolon_continues_tactic_rhs = bool(
            semicolon_idx != -1
            and _layout_local_let_rhs_starts_tactic_proof(rhs)
            and _looks_like_tactic_proof_continuation_line(
                candidate[semicolon_idx + 1 :]
            )
        )
        if (semicolon_idx == -1 or semicolon_continues_tactic_rhs) and not has_let_body_in:
            return True
        start = idx + len("let")


def _split_top_level_let_body(s: str) -> Optional[tuple[str, str]]:
    """Return ``(let_prefix, body)`` for a top-level local ``let`` expression."""
    raw = str(s or "").strip()
    if not raw.startswith("let"):
        return None
    assign_idx = _first_top_level_assign(raw)
    if assign_idx == -1:
        return None
    semicolon_idx = _first_top_level_semicolon(raw)
    body_start = -1
    if semicolon_idx != -1 and semicolon_idx > assign_idx + 1:
        body_start = semicolon_idx + 1
    else:
        in_idx = _first_top_level_keyword(raw, "in")
        if in_idx != -1 and in_idx > assign_idx + 1:
            body_start = in_idx + len("in")
    if body_start == -1:
        return None
    body = raw[body_start:].strip()
    if not body:
        return None
    return raw[:body_start].strip(), body


def _first_top_level_colon_after(s: str, start: int) -> int:
    """Return index of the first top-level ':' (excluding ':=') at or after *start*, or -1."""
    depth = 0
    i = max(0, int(start or 0))
    while i < len(s):
        skip_to = _lean_lexical_skip_end(s, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = s[i]
        if ch in _GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == ":" and depth == 0:
            if i + 1 < len(s) and s[i + 1] == "=":
                i += 1
                continue
            return i
        i += 1
    return -1


_SUBGOAL_DECL_HEAD_RE = re.compile(
    r"^(?:(?:noncomputable|private|protected|unsafe)\s+)*(?:theorem|lemma|example)\b"
)
_SUBGOAL_DECL_HEAD_WITH_KIND_RE = re.compile(
    r"^(?:(?:noncomputable|private|protected|unsafe)\s+)*"
    r"(?P<kind>theorem|lemma|example)\b"
)
_SUBGOAL_MARKER_INVALID_DECL_HEAD_RE = re.compile(
    r"^(?:(?:noncomputable|private|protected|unsafe)\s+)*"
    r"(?:theorem|lemma|example|def|abbrev|axiom|instance)\b"
)


def _strip_leading_decl_attributes(text: str) -> str:
    raw = _strip_leading_lean_comments(str(text or "").lstrip())
    while raw.startswith("@["):
        end = _scan_group(raw, 1)
        if end is None:
            break
        raw = _strip_leading_lean_comments(raw[end:].lstrip())
    return raw
_BINDER_IDENT_RE = re.compile(r"(?:[^\W\d_]|_)[\w']*", re.UNICODE)
_BINDER_KEYWORDS = frozenset(
    {
        "by",
        "fun",
        "match",
        "let",
        "have",
        "show",
        "theorem",
        "lemma",
        "example",
        "def",
        "abbrev",
        "forall",
        "exists",
        "True",
        "False",
        "Prop",
        "Type",
        "Nat",
        "Int",
        "Real",
        "Set",
        "Finset",
        "And",
        "Or",
        "Not",
        "Iff",
    },
)
_GROUP_OPEN_TO_CLOSE = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}


def _scan_group(text: str, start: int) -> Optional[int]:
    """Return the exclusive end index of a balanced group starting at *start*."""
    opener = text[start]
    closer = _GROUP_OPEN_TO_CLOSE.get(opener)
    if closer is None:
        return None
    stack = [closer]
    i = start + 1
    while i < len(text):
        skip_to = _lean_lexical_skip_end(text, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = text[i]
        if ch in _GROUP_OPEN_TO_CLOSE:
            stack.append(_GROUP_OPEN_TO_CLOSE[ch])
        elif stack and ch == stack[-1]:
            stack.pop()
            if not stack:
                return i + 1
        i += 1
    return None


def _canonicalize_interpolated_big_operator_binders(
    text: str,
    start: int,
) -> tuple[str, int]:
    """Canonicalize executable interpolation bodies, preserving literal text."""

    source = str(text or "")
    prefix = source[start : start + 3]
    out = [prefix]
    index = start + 3
    while index < len(source):
        if source[index] == "\\":
            out.append(source[index : min(len(source), index + 2)])
            index += 2
            continue
        if source[index] == '"':
            out.append('"')
            return "".join(out), index + 1
        if source.startswith("{{", index) or source.startswith("}}", index):
            out.append(source[index : index + 2])
            index += 2
            continue
        if source[index] != "{":
            out.append(source[index])
            index += 1
            continue
        expression_start = index + 1
        cursor = expression_start
        depth = 1
        while cursor < len(source):
            skip_to = _lean_lexical_skip_end(source, cursor)
            if skip_to is not None:
                cursor = max(cursor + 1, skip_to)
                continue
            if source[cursor] == "{":
                depth += 1
            elif source[cursor] == "}":
                depth -= 1
                if depth == 0:
                    out.append("{")
                    out.append(
                        _canonicalize_big_operator_binders(
                            source[expression_start:cursor]
                        )
                    )
                    out.append("}")
                    index = cursor + 1
                    break
            cursor += 1
        else:
            # Preserve malformed tails. Lean will reject them, while ordinary
            # safety validation still sees the complete source.
            out.append(source[index:])
            return "".join(out), len(source)
    return "".join(out), len(source)


def _canonicalize_big_operator_binders(stmt: str) -> str:
    """Rewrite planner-style ``∑ x in s, ...`` to accepted Lean syntax.

    Some models emit finite big-operator binders with ``in``. In the current
    Lean environment those statements fail to parse, while the equivalent
    membership form ``∑ x ∈ s, ...`` is accepted. Normalize this at subgoal
    ingestion so valid mathematical subgoals survive validation.
    """
    if not stmt or "in" not in stmt or not any(op in stmt for op in ("∑", "∏")):
        return stmt
    out: list[str] = []
    i = 0
    n = len(stmt)
    while i < n:
        if stmt.startswith(('s!"', 'm!"'), i):
            interpolated, interpolation_end = (
                _canonicalize_interpolated_big_operator_binders(stmt, i)
            )
            out.append(interpolated)
            i = max(i + 1, interpolation_end)
            continue
        skip_to = _lean_lexical_skip_end(stmt, i)
        if skip_to is not None:
            out.append(stmt[i:skip_to])
            i = skip_to
            continue
        ch = stmt[i]
        if ch not in ("∑", "∏"):
            out.append(ch)
            i += 1
            continue
        if stmt.startswith("∑'", i):
            out.append("∑'")
            i += 2
        else:
            out.append(ch)
            i += 1
        prefix_start = i
        while i < n:
            while i < n and stmt[i].isspace():
                i += 1
            if stmt.startswith(("/-", "--"), i):
                comment_end = _lean_lexical_skip_end(stmt, i)
                if comment_end is None or comment_end <= i:
                    break
                i = comment_end
                continue
            break
        out.append(stmt[prefix_start:i])
        if i >= n:
            break
        binder_start = i
        if stmt[i] in _GROUP_OPEN_TO_CLOSE:
            binder_end = _scan_group(stmt, i)
            if binder_end is None:
                out.append(stmt[i:])
                break
        else:
            binder_end = i
            while binder_end < n:
                if stmt.startswith(("/-", "--"), binder_end):
                    break
                skip_to = _lean_lexical_skip_end(stmt, binder_end)
                if skip_to is not None:
                    binder_end = skip_to
                    continue
                if stmt[binder_end].isspace() or stmt[binder_end] == ",":
                    break
                binder_end += 1
        out.append(stmt[binder_start:binder_end])
        i = binder_end
        ws_start = i
        while i < n:
            while i < n and stmt[i].isspace():
                i += 1
            if stmt.startswith(("/-", "--"), i):
                comment_end = _lean_lexical_skip_end(stmt, i)
                if comment_end is None or comment_end <= i:
                    break
                i = comment_end
                continue
            break
        out.append(stmt[ws_start:i])
        keyword_end = i + 2
        if stmt.startswith("in", i) and (
            keyword_end == n
            or not _is_lean_identifier_continue_char(stmt[keyword_end])
        ):
            out.append("∈")
            i = keyword_end
    return "".join(out)


def _canonicalize_top_level_let_in(stmt: str) -> str:
    """Rewrite planner-style top-level ``let ... in ...`` to Lean 4 syntax.

    Lean 4 theorem/goal types in this project use local lets as
    ``let x := value; body``. Planner models sometimes emit the Lean-3-ish
    spelling ``let x := value in body`` for a local let that appears after
    leading quantifiers. That spelling parses badly in helper declarations, so
    normalize only the top-level local-let body while leaving ordinary words
    named ``in`` and big-operator binders alone.
    """

    raw = str(stmt or "").strip()
    if not raw or "let" not in raw or "in" not in raw:
        return raw

    def convert_body(body: str) -> str:
        b = str(body or "").strip()
        paren_layers = 0
        inner = b
        while True:
            unwrapped = _unwrap_single_transparent_parens(inner)
            if unwrapped == inner:
                break
            paren_layers += 1
            inner = unwrapped
        if paren_layers:
            converted_inner = convert_body(inner)
            if converted_inner == inner:
                return b
            for _ in range(paren_layers):
                converted_inner = f"({converted_inner})"
            return converted_inner
        implication_prefix, conclusion = _split_top_level_implication_conclusion(b)
        if implication_prefix:
            converted_conclusion = convert_body(conclusion)
            if converted_conclusion != conclusion:
                return implication_prefix + converted_conclusion
            return b
        if not b.startswith("let"):
            return b
        assign_idx = _first_top_level_assign(b)
        if assign_idx == -1:
            return b
        semicolon_idx = _first_top_level_semicolon(b)
        in_idx = _top_level_local_let_body_in_index(b, assign_idx=assign_idx)
        if in_idx == -1 or in_idx <= assign_idx + 1:
            return b
        if semicolon_idx != -1 and semicolon_idx < in_idx:
            return b
        assigned_rhs = b[assign_idx + 2 : in_idx]
        converted_rhs = convert_body(assigned_rhs)
        return (
            f"{b[:assign_idx + 2].rstrip()} {converted_rhs}; "
            f"{b[in_idx + len('in'):].lstrip()}"
        )

    binders, body = _split_leading_forall_statement(raw)
    implication_prefix, conclusion = _split_top_level_implication_conclusion(
        body if binders else raw
    )
    converted = convert_body(conclusion)
    if converted == conclusion:
        return raw
    rebuilt = implication_prefix + converted
    if binders:
        return "".join(f"∀ {seg}, " for seg in binders) + rebuilt
    return rebuilt


def _top_level_token_positions(stmt: str, tokens: tuple[str, ...]) -> list[tuple[int, str]]:
    positions: list[tuple[int, str]] = []
    depth = 0
    i = 0
    while i < len(stmt):
        skip_to = _lean_lexical_skip_end(stmt, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = stmt[i]
        if ch in _GROUP_OPEN_TO_CLOSE:
            depth += 1
            i += 1
            continue
        if ch in _GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
            i += 1
            continue
        if depth == 0:
            matched = next((tok for tok in tokens if stmt.startswith(tok, i)), None)
            if matched is not None:
                positions.append((i, matched))
                i += len(matched)
                continue
        i += 1
    return positions


def _split_top_level_implication_conclusion(stmt: str) -> tuple[str, str]:
    """Split an implication chain before its terminal conclusion.

    Top-level arrows are consumed only until the remaining conclusion begins
    with a local ``let``.  Arrows inside grouping, comments, strings, and the
    local-let body therefore cannot move the split point.
    """

    raw = str(stmt or "").strip()
    if not raw:
        return "", ""
    conclusion_start = 0
    while conclusion_start < len(raw):
        significant_start = conclusion_start
        while significant_start < len(raw):
            while significant_start < len(raw) and raw[significant_start].isspace():
                significant_start += 1
            if not raw.startswith(("/-", "--"), significant_start):
                break
            comment_end = _lean_lexical_skip_end(raw, significant_start)
            if comment_end is None or comment_end <= significant_start:
                break
            significant_start = comment_end
        remaining = raw[significant_start:]
        if remaining.startswith("let") and (
            len(remaining) == len("let")
            or not _is_lean_identifier_continue_char(remaining[len("let")])
        ):
            conclusion_start = significant_start
            break
        arrow_source = raw[conclusion_start:]
        arrows = _top_level_token_positions(arrow_source, ("→", "->"))
        if not arrows:
            conclusion_start = significant_start
            break
        arrow_idx, arrow_token = arrows[0]
        conclusion_start += arrow_idx + len(arrow_token)
    return raw[:conclusion_start], raw[conclusion_start:].lstrip()


def _canonicalize_guarded_iff(stmt: str) -> str:
    """Parenthesize planner-style guarded equivalences.

    Lean parses ``H → A ↔ B`` as ``(H → A) ↔ B`` because ``→`` binds tighter
    than ``↔``.  LLM subgoal planners often use this shape for the mathematical
    convention ``H → (A ↔ B)``.  Keep the rewrite narrow: only apply it after
    explicit leading ``∀`` binders and only when the ambiguous arrow/iff tokens
    are both at top level.  Explicit ``(H → A) ↔ B`` remains untouched.
    """

    raw = str(stmt or "").strip()
    binders, body = _split_leading_forall_statement(raw)
    if not binders or not body:
        return raw
    iff_positions = _top_level_token_positions(body, ("↔", "<->"))
    if not iff_positions:
        return raw
    first_iff_idx = iff_positions[0][0]
    arrow_positions = [
        (idx, tok)
        for idx, tok in _top_level_token_positions(body, ("→", "->"))
        if idx < first_iff_idx
    ]
    if not arrow_positions:
        return raw
    arrow_idx, arrow_tok = arrow_positions[-1]
    right = body[arrow_idx + len(arrow_tok) :].strip()
    if not right or _unwrap_single_transparent_parens(right) != right:
        return raw
    guarded_body = f"{body[:arrow_idx + len(arrow_tok)].rstrip()} ({right})"
    return "".join(f"∀ {seg}, " for seg in binders) + guarded_body


def _strip_leading_lean_comments(text: str) -> str:
    raw = str(text or "").lstrip()
    while raw.startswith(("/-", "--")):
        end = _lean_lexical_skip_end(raw, 0)
        if end is None or end <= 0:
            break
        raw = raw[end:].lstrip()
    return raw


def _strip_lean_comments_from_header(text: str) -> str:
    raw = str(text or "")
    out: list[str] = []
    i = 0
    while i < len(raw):
        if raw.startswith(("/-", "--"), i):
            end = _lean_lexical_skip_end(raw, i)
            if end is None or end <= i:
                out.append(raw[i])
                i += 1
                continue
            if out and not out[-1].isspace():
                out.append(" ")
            elif not out:
                out.append(" ")
            i = end
            continue
        skip_to = _lean_lexical_skip_end(raw, i)
        if skip_to is not None:
            out.append(raw[i:skip_to])
            i = skip_to
            continue
        out.append(raw[i])
        i += 1
    return "".join(out)


def _strip_decl_name_from_header_tail(tail: str) -> str:
    raw = str(tail or "").strip()
    if not raw:
        return ""
    idx = 0
    n = len(raw)
    while idx < n:
        ch = raw[idx]
        if raw.startswith("«", idx):
            end = raw.find("»", idx + 1)
            if end == -1:
                return ""
            idx = end + 1
            continue
        if ch.isspace():
            return _strip_leading_lean_comments(raw[idx:].strip())
        if (
            ch in _GROUP_OPEN_TO_CLOSE
            and not (ch == "{" and idx > 0 and raw[idx - 1] == ".")
        ):
            return _strip_leading_lean_comments(raw[idx:].strip())
        if ch == "{" and idx > 0 and raw[idx - 1] == ".":
            end = _scan_group(raw, idx)
            if end is None:
                return ""
            idx = end
            continue
        idx += 1
    return ""


def _declaration_header_binders_before_colon(stmt: str, colon_idx: int) -> list[str]:
    """Return declaration binders that must become leading ``∀`` binders."""

    if colon_idx < 0:
        return []
    header = _strip_lean_comments_from_header(str(stmt or "")[:colon_idx]).strip()
    match = _SUBGOAL_DECL_HEAD_WITH_KIND_RE.match(header)
    if not match:
        return []
    kind = str(match.group("kind") or "").strip()
    tail = header[match.end() :].strip()
    if kind in {"theorem", "lemma"}:
        tail = _strip_decl_name_from_header_tail(tail)
    if not tail:
        return []
    return [
        segment
        for segment in _split_binder_segment(tail)
        if str(segment or "").strip()
    ]


def _prepend_declaration_binders(stmt: str, decl_binders: Sequence[str]) -> str:
    raw_stmt = str(stmt or "").strip()
    if not raw_stmt:
        return ""
    ordered = [
        str(seg or "").strip()
        for seg in _split_binder_segments(decl_binders)
        if str(seg or "").strip()
    ]
    prefix = build_forall_prefix_from_binders(ordered, max_prefix_chars=0)
    if not prefix:
        return raw_stmt
    return f"{prefix}, {raw_stmt}"


def normalize_subgoal_statement(
    stmt: str,
    *,
    canonicalize_guarded_iff: bool = True,
) -> str:
    """Normalize common declaration-wrapped planner subgoals.

    Example:
      `theorem subgoal1 : ∀ n, p n ≤ q n := by sorry`
      -> `∀ n, p n ≤ q n`
    """
    s = (stmt or "").strip()
    if not s:
        return ""
    s = _rendered_turnstile_target_payload(s)
    if _has_hard_lowercase_subgoal_label_boundary(s):
        return ""

    decl_candidate = _strip_leading_decl_attributes(s)
    if _SUBGOAL_DECL_HEAD_RE.match(decl_candidate):
        s = decl_candidate
        colon_idx = _first_top_level_colon(s)
        if colon_idx != -1:
            decl_binders = _declaration_header_binders_before_colon(s, colon_idx)
            s = s[colon_idx + 1 :].strip()
            s = _strip_trailing_declaration_proof_assign(s)
            s = _strip_trailing_subgoal_explanation_lines(s)
            if decl_binders:
                s = _prepend_declaration_binders(s, decl_binders) or s

    paren_layers = 0
    paren_inner = s
    while True:
        unwrapped = _unwrap_single_transparent_parens(paren_inner)
        if unwrapped == paren_inner:
            break
        paren_layers += 1
        paren_inner = unwrapped
    if paren_layers:
        stripped_inner = _strip_trailing_declaration_proof_assign(paren_inner)
        if stripped_inner != paren_inner:
            s = stripped_inner
            for _ in range(paren_layers):
                s = f"({s})"

    assign_idx = _first_top_level_assign(s)
    _binders, body = _split_leading_forall_statement(s)
    body_candidate = (body or s).strip()
    _implication_prefix, conclusion_candidate = (
        _split_top_level_implication_conclusion(body_candidate)
    )
    preserve_local_let = s.startswith("let ") or _looks_like_top_level_let_expression(s) or (
        conclusion_candidate.startswith("let")
        and _looks_like_top_level_let_expression(conclusion_candidate)
    )
    if assign_idx != -1:
        lhs = s[:assign_idx].rstrip()
        rhs = s[assign_idx + 2 :].strip()
        # Preserve local `let ... := ...; ...` style expressions; their
        # top-level assignment is part of the statement, not a declaration
        # wrapper.  Also preserve truncated `:=` tails so validation can fail
        # closed instead of silently turning malformed statements into
        # apparently valid binder-only theorems.
        stripped = _strip_trailing_declaration_proof_assign(s)
        if stripped != s:
            s = stripped
        elif not preserve_local_let and _first_top_level_semicolon(s) == -1 and rhs:
            # A top-level `:=` in a type expression separates the statement
            # (LHS) from an attached proof term.  Strip the RHS for
            # declaration-shaped planner echoes like `... := by sorry`.
            s = lhs

    s = _strip_trailing_subgoal_explanation_lines(s)
    s = _canonicalize_big_operator_binders(s)
    if canonicalize_guarded_iff:
        s = _canonicalize_guarded_iff(s)
    return s


def extract_leading_forall_binders(statement: str) -> list[str]:
    """Extract leading `∀` binder segments from a Lean type expression.

    Returns a list of binder segments (without the leading `∀` and comma).
    Stops when the remaining body no longer begins with a plain `∀` binder.
    Eventual quantifiers like `∀ᶠ` are preserved as part of the body.
    """
    binders: list[str] = []
    rest = (statement or "").strip()
    while rest.startswith("∀") and not rest.startswith("∀ᶠ"):
        tail = rest[1:].lstrip()
        comma_idx = _first_top_level_comma(tail)
        if comma_idx == -1:
            break
        segment = tail[:comma_idx].strip()
        if segment:
            binders.append(segment)
        rest = tail[comma_idx + 1 :].strip()
    return binders


_RELATION_FORALL_BINDER_OPS: tuple[tuple[str, str], ...] = (
    ("∉", "not_mem"),
    ("∈", "mem"),
    ("≥", "ge"),
    (">=", "ge"),
    ("≤", "le"),
    ("<=", "le"),
    ("≠", "ne"),
    ("!=", "ne"),
    (">", "gt"),
    ("<", "lt"),
    ("=", "eq"),
)


def _split_relation_forall_binder_segment(
    segment: str,
) -> Optional[tuple[str, str, str, str]]:
    """Split Lean shorthand binders like ``n ≥ 2`` or ``x ∈ s``.

    Lean accepts ``∀ n ≥ 2, P n`` as shorthand for a variable binder plus a
    proposition-valued assumption.  The mini subgoal compiler needs the latter
    shape when it closes helper claims over root hypotheses.
    """

    raw = str(segment or "").strip()
    if not raw or raw[0] in "({[⦃" or ":" in raw:
        return None
    depth = 0
    i = 0
    while i < len(raw):
        ch = raw[i]
        if ch in "([{⦃":
            depth += 1
            i += 1
            continue
        if ch in ")]}⦄":
            depth = max(0, depth - 1)
            i += 1
            continue
        if depth == 0:
            for op, label in _RELATION_FORALL_BINDER_OPS:
                if not raw.startswith(op, i):
                    continue
                left = raw[:i].strip()
                right = raw[i + len(op) :].strip()
                if not left or not right:
                    continue
                names = list(_BINDER_IDENT_RE.findall(left))
                if len(names) != 1 or names[0] != left:
                    continue
                return names[0], op, label, right
        i += 1
    return None


def _unique_context_hypothesis_name(
    base_name: str,
    *,
    used_names: Set[str],
) -> str:
    base = re.sub(r"[^A-Za-z0-9_']+", "_", str(base_name or "")).strip("_")
    if not base or base[0].isdigit():
        base = f"h_{base or 'rel'}"
    candidate = base
    suffix = 2
    while candidate in used_names:
        candidate = f"{base}_{suffix}"
        suffix += 1
    used_names.add(candidate)
    return candidate


def _relation_hypothesis_name(
    var_name: str,
    label: str,
    *,
    used_names: Set[str],
) -> str:
    return _unique_context_hypothesis_name(
        f"h_{var_name}_{label}",
        used_names=used_names,
    )


def _leading_implication_assumption_binders(
    body: str,
    *,
    used_names: Set[str],
) -> list[str]:
    binders: list[str] = []
    current = str(body or "").strip()
    index = 1
    while current:
        split = _split_top_level(current, "→") or _split_top_level(current, "->")
        if split is None:
            break
        premise, current = split
        premise = str(premise or "").strip()
        if not premise:
            break
        hyp_name = _unique_context_hypothesis_name(
            f"h_root_{index}",
            used_names=used_names,
        )
        binders.append(f"({hyp_name} : {premise})")
        index += 1
    return binders


def expand_relation_forall_binders(statement: str) -> list[str]:
    """Return leading root-context binders with hypotheses made explicit.

    Example:
      ``∀ n ≥ 2, P n`` contributes ``["n", "(h_n_ge : n ≥ 2)"]``.
      ``∀ (n : ℕ), 2 ≤ n → P n`` contributes
      ``["(n : ℕ)", "(h_root_1 : 2 ≤ n)"]``.

    This preserves the theorem's local assumptions when a helper claim mentions
    root variables but does not restate their hypotheses.
    """

    expanded: list[str] = []
    used_names: Set[str] = set()
    segments, body = _split_leading_forall_statement(statement)
    for segment in segments:
        split = _split_relation_forall_binder_segment(segment)
        if split is None:
            expanded.append(segment)
            used_names.update(_declared_names_from_binder_segments([segment]))
            continue
        var_name, op, label, right = split
        hyp_name = _relation_hypothesis_name(
            var_name,
            label,
            used_names=used_names,
        )
        expanded.append(var_name)
        expanded.append(f"({hyp_name} : {var_name} {op} {right})")
        used_names.add(var_name)
    expanded.extend(
        _leading_implication_assumption_binders(body, used_names=used_names)
    )
    return expanded


def _split_leading_forall_statement(statement: str) -> tuple[list[str], str]:
    binders: list[str] = []
    rest = (statement or "").strip()
    while rest.startswith("∀") and not rest.startswith("∀ᶠ"):
        tail = rest[1:].lstrip()
        comma_idx = _first_top_level_comma(tail)
        if comma_idx == -1:
            break
        segment = tail[:comma_idx].strip()
        if segment:
            binders.append(segment)
        rest = tail[comma_idx + 1 :].strip()
    return binders, rest


def _extract_leading_quantifier_binders(statement: str) -> list[str]:
    binders: list[str] = []
    rest = (statement or "").strip()
    while rest.startswith(("∀", "∃")):
        if rest.startswith("∀ᶠ"):
            break
        tail = rest[1:].lstrip()
        comma_idx = _first_top_level_comma(tail)
        if comma_idx == -1:
            break
        segment = tail[:comma_idx].strip()
        if segment:
            binders.append(segment)
        rest = tail[comma_idx + 1 :].strip()
    return binders


def _telescope_quantifier_bound_names(statement: str) -> set[str]:
    """Names bound by leading ∀/∃ and nested quantifiers after a top-level →."""
    names: set[str] = set()
    rest = str(statement or "").strip()
    while rest:
        if rest.startswith("∀ᶠ"):
            break
        if rest.startswith(("∀", "∃")):
            binders = _extract_leading_quantifier_binders(rest)
            names |= _declared_names_from_binder_segments(
                _split_binder_segments(binders)
            )
            if rest.startswith("∃"):
                # `_split_leading_forall_statement` does not consume ∃.
                break
            _, after = _split_leading_forall_statement(rest)
            if after == rest:
                break
            rest = after
            continue
        split = _split_top_level(rest, "→") or _split_top_level(rest, "->")
        if split is None:
            break
        _premise, conclusion = split
        conclusion = conclusion.strip()
        if not conclusion.startswith(("∀", "∃")):
            break
        rest = conclusion
    return names


def _binder_identifier_tokens(text: str) -> set[str]:
    if not text:
        return set()
    return {
        tok
        for tok in _BINDER_IDENT_RE.findall(text)
        if tok and tok not in _BINDER_KEYWORDS
    }


def make_forall_binders_explicit(statement: str) -> str:
    """Rewrite implicit / instance binders in every quantifier to explicit form.

    The orchestrator's scaffold-slot pipeline preserves the exact binder
    syntax Lean reports for a hole, including ``{S : Type u_2}`` (implicit),
    ``[Mul S]`` (instance-implicit), and ``⦃a : α⦄`` (strict-implicit).
    Lean's ``intro`` tactic does not present implicit / instance / strict-
    implicit binders to the user — they're auto-bound by elaboration. The
    LLM, looking at the statement text, doesn't make that distinction and
    emits ``intro S inst hS a x y h`` for what looks like seven binders.
    After Lean elaborates the auto-bound binders away, only the explicit
    ones remain, and ``intro S`` fails with::

        Tactic `introN` failed: There are no additional binders or `let`
        bindings in the goal to introduce

    The reproducer is putnam_2001_a1's slot:critical_validated_1 cascade
    (see runs/live_traces/2001_a1_16apr_5.jsonl: 36 binder_arity_mismatch
    rejections in a single slot dispatch).

    Fix: walk every quantifier (``∀``/``∃`` and the ASCII fallbacks
    ``forall``/``exists``) and rewrite ``{x : T}`` → ``(x : T)``,
    ``[x : T]`` → ``(x : T)``, and ``⦃x : T⦄`` → ``(x : T)``. Anonymous
    instance binders ``[T]`` get a synthetic name ``_inst_N``. The resulting
    type is propositionally equivalent (visibility is only a calling-
    convention distinction in Lean 4); both Lean's elaborator and the LLM's
    ``intro`` see the same explicit binder count.

    The walker handles:
      * Mixed binder visibility within one quantifier:
        ``∀ (x : T) {y : U}, P`` → ``∀ (x : T) (y : U), P``
      * Multiple groups of any visibility: ``∀ {a} ⦃b⦄ [C], P``
      * Nested quantifiers: ``∀ {S}, (∀ {a : S}, a = a) → True``
      * Set singletons in non-binder position are NOT touched.
    """
    src = str(statement or "")
    if not src:
        return src
    # Cheap pre-filter: skip work if no implicit-binder markers anywhere.
    if "{" not in src and "[" not in src and "⦃" not in src:
        return src

    # Quantifier head detection: a position immediately after one of
    # these tokens is a binder-group sequence until the next top-level
    # comma. ASCII forms must be followed by whitespace to avoid matching
    # identifiers like `forall_intro`.
    out: List[str] = []
    i = 0
    n = len(src)
    inst_seq = 0

    def _at_quantifier(pos: int) -> int:
        """Return length of quantifier head at pos (0 if none)."""
        if pos >= n:
            return 0
        ch = src[pos]
        if ch in ("∀", "∃"):
            return 1
        # ASCII fallbacks — must be a whole word
        for kw in ("forall", "exists"):
            if src.startswith(kw, pos):
                end = pos + len(kw)
                if end >= n or not (src[end].isalnum() or src[end] == "_"):
                    return len(kw)
        return 0

    while i < n:
        head_len = _at_quantifier(i)
        if head_len == 0:
            out.append(src[i])
            i += 1
            continue
        # Emit the quantifier head as-is, advance past whitespace
        out.append(src[i : i + head_len])
        i += head_len
        while i < n and src[i].isspace():
            out.append(src[i])
            i += 1
        # Loop through every binder group up to the next top-level
        # comma. Each group is one of: (...), {...}, [...], or ⦃...⦄.
        # Convert `{...}`, `[...]`, and `⦃...⦄` to `(...)`. Pass `(...)`
        # through unchanged. Stop on top-level comma.
        while i < n:
            # Bail out if we hit the comma that ends the binder list.
            if src[i] == ",":
                break
            if src[i].isspace():
                out.append(src[i])
                i += 1
                continue
            ch = src[i]
            if ch == "(":
                # Explicit binder group — pass through verbatim.
                end = _scan_group(src, i)
                if end is None:
                    out.append(src[i])
                    i += 1
                    continue
                out.append(src[i:end])
                i = end
                continue
            if ch in ("{", "["):
                opener = ch
                end = _scan_group(src, i)
                if end is None:
                    out.append(src[i])
                    i += 1
                    continue
                inner = src[i + 1 : end - 1].strip()
                if opener == "[" and ":" not in inner:
                    inst_seq += 1
                    inner = f"_inst_{inst_seq} : {inner}"
                out.append("(")
                out.append(inner)
                out.append(")")
                i = end
                continue
            if ch == "⦃":
                # Strict-implicit binder ⦃x : T⦄ — find matching ⦄.
                end = src.find("⦄", i + 1)
                if end == -1:
                    out.append(src[i])
                    i += 1
                    continue
                inner = src[i + 1 : end].strip()
                out.append("(")
                out.append(inner)
                out.append(")")
                i = end + 1
                continue
            # Any other character (identifier start, etc.) means we're
            # past the binder list. Bail to outer loop.
            break
    return "".join(out)


def _split_binder_segment(segment: str) -> list[str]:
    out: list[str] = []
    rest = str(segment or "").strip()
    if not rest:
        return out
    i = 0
    n = len(rest)
    while i < n:
        while i < n and rest[i].isspace():
            i += 1
        if i < n and rest.startswith(("/-", "--"), i):
            end = _lean_lexical_skip_end(rest, i)
            if end is None or end <= i:
                break
            i = end
            continue
        if i >= n:
            break
        if rest[i] not in _GROUP_OPEN_TO_CLOSE:
            out.append(rest[i:].strip())
            break
        end = _scan_group(rest, i)
        if end is None:
            out.append(rest[i:].strip())
            break
        out.append(rest[i:end].strip())
        i = end
    return out


_UNIVERSE_TOKEN_RE = re.compile(
    r"\b(Type|Sort)(\.\{)?(\s*\(?\s*)([a-z][A-Za-z0-9_']*)\b"
)
_UNIVERSE_TOKEN_STOPLIST = frozenset(
    {"max", "imax", "of", "Type", "Sort", "Prop", "in", "let", "fun", "do"}
)


def normalize_free_universes_to_canonical(statement: str) -> str:
    """Rewrite every free universe identifier in `statement` to a single
    canonical name `u`.

    Lean's hole reporter assigns FRESH universe variables per capture
    (slot_1 → ``Type u_2``, slot_2 → ``Type u_3``). When the orchestrator
    stitches a slot's target by prepending dependency signatures, the
    independently-named universes become LITERAL distinct universe
    parameters in the stitched Π-type. Any application that needs both
    universes to coincide (e.g. ``slot_1_inj_leftMul S`` where ``S``
    comes from slot_2's body) fails with ``Application type mismatch:
    argument has type Type u_3 but expected Type u_2``.

    Live trace 2001_a1_16apr_9.jsonl: 32 distinct slot_2 proofs were
    semantically correct but failed because the planner-stitched
    statement made slot_1 universe-incompatible with slot_2's body.

    Renaming all free universe names to the same canonical token forces
    Lean to elaborate them as the SAME universe parameter, so the
    application unifies. This is safe because:

    1. The canonical token is declared via `_free_universe_decl` which
       collects whatever names appear post-rename.
    2. Universe parameters in distinct binders that genuinely should be
       distinct cannot occur in a stitched slot.target — Lean's hole
       reporter never emits multiple distinct universe parameters for a
       single goal; multiple `u_N` ALWAYS arise from independent capture
       and ALWAYS need to coincide.
    """
    src = str(statement or "")
    if not src:
        return src
    if "Type" not in src and "Sort" not in src:
        return src

    def _replace(match: re.Match[str]) -> str:
        name = match.group(4)
        if not name or name in _UNIVERSE_TOKEN_STOPLIST:
            return match.group(0)
        sort_kw = match.group(1)
        dot_brace = match.group(2) or ""
        spacing = match.group(3) or " "
        return f"{sort_kw}{dot_brace}{spacing}u"

    return _UNIVERSE_TOKEN_RE.sub(_replace, src)


def _split_binder_segments(binders: Sequence[str]) -> list[str]:
    out: list[str] = []
    for seg in binders:
        out.extend(_split_binder_segment(seg))
    return out


def _binder_segment_parts(segment: str) -> tuple[str, str, str]:
    raw = str(segment or "").strip()
    if not raw:
        return "", "", ""
    if raw[0] not in _GROUP_OPEN_TO_CLOSE:
        return "", raw, ""
    end = _scan_group(raw, 0)
    if end != len(raw):
        return "", raw, ""
    opener = raw[0]
    closer = _GROUP_OPEN_TO_CLOSE[opener]
    return opener, raw[1:-1].strip(), closer


def _declared_names_from_binder_segments(binders: Sequence[str]) -> set[str]:
    declared: set[str] = set()
    for seg in binders:
        raw = str(seg or "").strip()
        if not raw:
            continue
        opener, inner, _closer = _binder_segment_parts(raw)
        content = inner if opener else raw
        if opener == "[" and _first_top_level_colon(content) == -1:
            continue
        if ":=" in content:
            content = content.split(":=", 1)[0].strip()
        colon_idx = _first_top_level_colon(content)
        # Membership binders (x ∈ s) use ∈ as a delimiter analogous to :.
        if colon_idx == -1:
            mem_idx = content.find("∈")
            if mem_idx != -1:
                colon_idx = mem_idx
        head = content[:colon_idx].strip() if colon_idx != -1 else content.strip()
        declared.update(_binder_identifier_tokens(head))
    return declared


def _binder_segment_declared_names(segment: str) -> list[str]:
    raw = str(segment or "").strip()
    if not raw:
        return []
    opener, inner, _closer = _binder_segment_parts(raw)
    content = inner if opener else raw
    if opener == "[" and _first_top_level_colon(content) == -1:
        return []
    if ":=" in content:
        content = content.split(":=", 1)[0].strip()
    colon_idx = _first_top_level_colon(content)
    # Membership binders (x ∈ s) use ∈ as a delimiter analogous to :.
    if colon_idx == -1:
        mem_idx = content.find("∈")
        if mem_idx != -1:
            colon_idx = mem_idx
    head = content[:colon_idx].strip() if colon_idx != -1 else content.strip()
    out: list[str] = []
    seen: set[str] = set()
    for tok in re.split(r"\s+", head):
        name = str(tok or "").strip().strip(",")
        if not name or name == "_" or name in seen:
            continue
        if name in _BINDER_KEYWORDS:
            continue
        if not _binder_identifier_tokens(name):
            continue
        seen.add(name)
        out.append(name)
    return out


def _declared_name_annotations_from_binder_segments(
    binders: Sequence[str],
) -> dict[str, str]:
    out: dict[str, str] = {}
    for seg in binders:
        annotation = normalize_statement(_binder_segment_annotation(seg))
        if not annotation:
            continue
        for name in _binder_segment_declared_names(seg):
            out.setdefault(name, annotation)
    return out


def _binder_segment_referenced_names(segment: str) -> set[str]:
    raw = str(segment or "").strip()
    if not raw:
        return set()
    opener, inner, _closer = _binder_segment_parts(raw)
    content = inner if opener else raw
    if ":=" in content:
        content = content.split(":=", 1)[0].strip()
    colon_idx = _first_top_level_colon(content)
    # Membership binders (x ∈ s) use ∈ as a delimiter analogous to :.
    if colon_idx == -1:
        mem_idx = content.find("∈")
        if mem_idx != -1:
            colon_idx = mem_idx
    body = content[colon_idx + 1 :].strip() if colon_idx != -1 else content.strip()
    if not body:
        return set()
    nested_declared = _declared_names_from_binder_segments(
        _extract_leading_quantifier_binders(body)
    )
    return (
        _binder_identifier_tokens(body)
        - nested_declared
        - set(_binder_segment_declared_names(segment))
    )


def _binder_segment_annotation(segment: str) -> str:
    raw = str(segment or "").strip()
    if not raw:
        return ""
    opener, inner, _closer = _binder_segment_parts(raw)
    content = inner if opener else raw
    if ":=" in content:
        content = content.split(":=", 1)[0].strip()
    colon_idx = _first_top_level_colon(content)
    if colon_idx == -1:
        return ""
    return content[colon_idx + 1 :].strip()


def _binder_name_looks_like_instance(name: str) -> bool:
    compact = str(name or "").strip().lstrip("_")
    return bool(compact) and compact.startswith("inst")


def _binder_name_looks_like_simple_term_param(name: str) -> bool:
    compact = str(name or "").strip().lstrip("_")
    return len(compact) == 1 and compact.islower()


def _binder_segment_looks_supporting_assumption(
    segment: str,
    *,
    dependency_names: Optional[Set[str]] = None,
    dependency_annotations: Optional[dict[str, str]] = None,
) -> bool:
    raw = str(segment or "").strip()
    if not raw:
        return False
    opener, _inner, _closer = _binder_segment_parts(raw)
    if opener == "[":
        # Instance binders are ambient support, not part of the substantive
        # claim. Preserve them when we close a local goal into a theorem.
        return True
    annotation = normalize_statement(_binder_segment_annotation(raw))
    if not annotation:
        return False
    if annotation.startswith(("Prop", "True", "False", "∀", "∃", "¬")):
        return True
    if any(
        token in annotation
        for token in (
            " = ",
            " ≠ ",
            " < ",
            " > ",
            " ≤ ",
            " ≥ ",
            " ∈ ",
            " ∉ ",
            " ⊆ ",
            " ⊂ ",
            " ⊇ ",
            " ⊃ ",
            " → ",
            " ↔ ",
            " -> ",
            "<->",
            "∧",
            "∨",
            "∣",
        )
    ):
        return True
    declared = _binder_segment_declared_names(raw)
    if declared and all(_binder_name_looks_like_instance(name) for name in declared):
        return True
    if declared and all(name.startswith("h") for name in declared):
        return True
    deps = {
        str(name or "").strip()
        for name in (dependency_names or set())
        if str(name or "").strip()
    }
    if not deps:
        return False
    if declared and not all(
        _binder_name_looks_like_simple_term_param(name) for name in declared
    ):
        return True
    if len(deps) == 1:
        dep_name = next(iter(deps))
        dep_ann = normalize_statement(
            str((dependency_annotations or {}).get(dep_name, "") or "")
        )
        if annotation == dep_name and dep_ann == "Prop":
            return True
    return False


def _normalize_binder_segment(segment: str) -> str:
    raw = str(segment or "").strip()
    if not raw:
        return ""
    return raw if raw.startswith(("(", "{", "[")) else f"({raw})"


def _rebuild_binder_segment(segment: str, names: Sequence[str]) -> str:
    raw = str(segment or "").strip()
    if not raw:
        return ""
    name_list = [str(name or "").strip() for name in names if str(name or "").strip()]
    if not name_list:
        return ""
    opener, inner, closer = _binder_segment_parts(raw)
    content = inner if opener else raw
    if ":=" in content:
        content = content.split(":=", 1)[0].strip()
    colon_idx = _first_top_level_colon(content)
    rebuilt_inner = " ".join(name_list)
    if colon_idx != -1:
        rebuilt_inner += " " + content[colon_idx:].lstrip()
    if opener and closer:
        return f"{opener}{rebuilt_inner}{closer}"
    return rebuilt_inner


def select_contextual_binders(
    stmt: str,
    binders: Sequence[str],
    *,
    needed_names: Optional[Set[str]] = None,
    include_supporting_assumptions: bool = False,
) -> list[str]:
    """Pick the smallest dependency-closed binder prefix needed for *stmt*.

    Once a later binder is selected, keep the full prefix leading to it so
    earlier hypotheses remain available as ambient assumptions instead of being
    silently dropped.
    """
    raw_stmt = str(stmt or "").strip()
    raw_binders = _split_binder_segments(_extract_leading_quantifier_binders(raw_stmt))
    leading_declared = _declared_names_from_binder_segments(raw_binders)
    local_declared = _telescope_quantifier_bound_names(raw_stmt)
    nested_declared = local_declared - leading_declared
    flattened = _split_binder_segments(binders)
    if needed_names is None:
        context_declared = _declared_names_from_binder_segments(flattened)
        used = _binder_identifier_tokens(raw_stmt)
        needed = (used & context_declared) - local_declared
    else:
        needed = {str(name).strip() for name in needed_names if str(name).strip()}
    if not flattened or not needed:
        return []

    items: list[tuple[str, set[str], set[str], str]] = []
    seen_keys: set[str] = set()
    for seg in flattened:
        declared_order = _binder_segment_declared_names(seg)
        if declared_order:
            remaining_names = [
                name for name in declared_order if name not in local_declared
            ]
            if not remaining_names:
                continue
            kept_segment = (
                seg.strip()
                if len(remaining_names) == len(declared_order)
                else _rebuild_binder_segment(seg, remaining_names)
            )
            declared_names = set(remaining_names)
        else:
            kept_segment = str(seg or "").strip()
            declared_names = set()
        normalized_key = _normalize_binder_segment(kept_segment)
        if not normalized_key or normalized_key in seen_keys:
            continue
        raw_referenced_names = _binder_segment_referenced_names(seg)
        if raw_referenced_names & nested_declared:
            # Cannot merge into the leading ∀: the annotation mentions a name
            # bound only after a later top-level implication.
            continue
        seen_keys.add(normalized_key)
        referenced_names = raw_referenced_names - local_declared
        items.append((kept_segment, declared_names, referenced_names, normalized_key))

    selected_indices: set[int] = set()
    selected_keys: set[str] = set()
    required_names = set(needed)
    for idx in range(len(items) - 1, -1, -1):
        segment, declared_names, referenced_names, normalized_key = items[idx]
        include = False
        if declared_names:
            include = bool(declared_names & required_names)
        else:
            include = bool(referenced_names & required_names)
        if not include or normalized_key in selected_keys:
            continue
        selected_indices.add(idx)
        selected_keys.add(normalized_key)
        required_names.update(referenced_names)

    if not selected_indices:
        return []
    prefix_end = max(selected_indices)
    selected: set[int] = set(range(prefix_end + 1))
    dependency_names = set(local_declared)
    dependency_annotations = _declared_name_annotations_from_binder_segments(
        raw_binders
    )
    for _segment, declared_names, _referenced_names, _normalized_key in items:
        dependency_names.update(declared_names)
    dependency_annotations.update(
        _declared_name_annotations_from_binder_segments(
            [
                segment
                for segment, _declared_names, _referenced_names, _normalized_key in items
            ]
        )
    )
    if include_supporting_assumptions:
        available_names: set[str] = set(local_declared)
        for idx in selected:
            available_names.update(items[idx][1])
        changed = True
        while changed:
            changed = False
            for idx in range(prefix_end + 1, len(items)):
                if idx in selected:
                    continue
                segment, declared_names, referenced_names, _normalized_key = items[idx]
                required_dependencies = referenced_names & dependency_names
                if not _binder_segment_looks_supporting_assumption(
                    segment,
                    dependency_names=required_dependencies,
                    dependency_annotations=dependency_annotations,
                ):
                    continue
                if required_dependencies - available_names:
                    continue
                selected.add(idx)
                available_names.update(declared_names)
                changed = True
    return [items[idx][0] for idx in range(len(items)) if idx in selected]


def merge_contextual_binders(
    stmt: str,
    binders: Sequence[str],
    *,
    max_prefix_chars: int = 600,
) -> Optional[str]:
    """Merge selected context binders into a statement's leading `∀` chain."""
    raw_stmt = str(stmt or "").strip()
    if not raw_stmt:
        return None
    raw_segments, body = _split_leading_forall_statement(raw_stmt)
    merged: list[list[Any]] = []
    seen_keys: set[str] = set()
    declared_names: set[str] = set()
    for seg in _split_binder_segments(raw_segments):
        raw = str(seg or "").strip()
        if not raw:
            continue
        normalized_key = _normalize_binder_segment(raw)
        if not normalized_key or normalized_key in seen_keys:
            continue
        seen_keys.add(normalized_key)
        declared_segment_names = set(_binder_segment_declared_names(raw))
        merged.append(
            [
                raw,
                declared_segment_names,
                _binder_segment_referenced_names(raw),
                True,
            ]
        )
        declared_names.update(declared_segment_names)
    inserted = False
    for seg in _split_binder_segments(binders):
        raw = str(seg or "").strip()
        if not raw:
            continue
        declared_order = _binder_segment_declared_names(raw)
        if declared_order:
            remaining_names = [
                name for name in declared_order if name not in declared_names
            ]
            if not remaining_names:
                continue
            kept_segment = (
                raw
                if len(remaining_names) == len(declared_order)
                else _rebuild_binder_segment(raw, remaining_names)
            )
            declared_segment_names = set(remaining_names)
        else:
            kept_segment = raw
            declared_segment_names = set()
        normalized_key = _normalize_binder_segment(kept_segment)
        if not normalized_key or normalized_key in seen_keys:
            continue
        referenced_names = _binder_segment_referenced_names(raw)
        target_names = declared_segment_names or referenced_names
        insert_at = len(merged)
        for idx, (_seg, _declared, _referenced, is_local) in enumerate(merged):
            if not is_local:
                continue
            if target_names and (_referenced & target_names):
                insert_at = idx
                break
        merged.insert(
            insert_at,
            [
                kept_segment,
                declared_segment_names,
                referenced_names,
                False,
            ],
        )
        declared_names.update(declared_segment_names)
        seen_keys.add(normalized_key)
        inserted = True
    if not inserted:
        return None
    prefix = build_forall_prefix_from_binders(
        [item[0] for item in merged],
        max_prefix_chars=max_prefix_chars,
    )
    if not prefix:
        return None
    merged_stmt = f"{prefix}, {body}" if body else prefix
    if normalize_subgoal_statement(merged_stmt) == normalize_subgoal_statement(
        raw_stmt
    ):
        return None
    return merged_stmt


def build_forall_prefix_from_binders(
    binders: list[str] | tuple[str, ...],
    *,
    max_prefix_chars: int = 600,
) -> Optional[str]:
    """Build a syntactically valid `∀` binder prefix from extracted segments."""
    # Lean accepts bare binders like `∀ n, ...` and bare groups like `∀ a b, ...`.
    # Wrapping those as `∀ (n), ...` is invalid syntax, so only parenthesize when
    # the segment is not a simple identifier/group.
    bare_group_re = re.compile(
        r"^(?:[^\W\d_]|_)[\w']*(?:\s+(?:[^\W\d_]|_)[\w']*)*$", re.UNICODE
    )
    seen: set[str] = set()
    cleaned: list[str] = []
    for seg in binders:
        raw = str(seg or "").strip()
        if not raw:
            continue
        if raw.startswith(tuple(_GROUP_OPEN_TO_CLOSE)):
            rendered = raw
        elif ":" not in raw and ":=" not in raw and bare_group_re.fullmatch(raw):
            rendered = raw
        else:
            rendered = f"({raw})"
        if rendered in seen:
            continue
        seen.add(rendered)
        cleaned.append(rendered)
    if not cleaned:
        return None
    prefix = "∀ " + " ".join(cleaned)
    if max_prefix_chars > 0 and len(prefix) > max_prefix_chars:
        return None
    return prefix


def contextualize_subgoal_with_binders(
    stmt: str,
    root_statement: str,
    *,
    max_prefix_chars: int = 600,
) -> Optional[str]:
    """Prefix a subgoal with leading binders from the root statement.

    Returns a new statement when a safe binder prefix is available, else None.
    """
    if not stmt or not root_statement:
        return None
    binders = extract_leading_forall_binders(root_statement)
    if not binders:
        return None
    binders = select_contextual_binders(
        stmt,
        binders,
        include_supporting_assumptions=True,
    )
    if not binders:
        return None
    merged = merge_contextual_binders(
        stmt.strip(),
        binders,
        max_prefix_chars=max_prefix_chars,
    )
    if merged:
        return merged
    prefix = build_forall_prefix_from_binders(
        binders,
        max_prefix_chars=max_prefix_chars,
    )
    if not prefix:
        return None
    return f"{prefix}, {stmt.strip()}"


def _looks_like_reasoning_symbolic_prose_fragment(s: str) -> bool:
    stripped = str(s or "").strip()
    if not stripped:
        return False
    if re.match(r"^[A-Za-z_][A-Za-z0-9_']*:\s+", stripped):
        return True
    formal_head = stripped
    while True:
        unwrapped = _unwrap_single_transparent_parens(formal_head)
        if unwrapped == formal_head:
            break
        formal_head = unwrapped
    if formal_head.startswith(("∀", "∃")) or re.match(
        r"(?i)^(?:forall|exists)\b", formal_head
    ):
        return False
    if re.match(
        r"(?s)^(?:goal|target|claim|subgoal)\s*(?:=|≠|≤|≥|<|>|∈|∉|⊆|∣)\s*.+$",
        stripped,
    ):
        return False
    phrase = re.sub(r"[-_]+", " ", stripped)
    planner_head = (
        r"(?:(?:remaining|current|target|the|this)\s+){0,3}"
        r"(?:goals?|targets?|subgoals?|claims?)"
    )
    planner_tail = re.match(
        rf"(?is)^{planner_head}"
        r"(?:\s*:|\s+(?:is|are|remains?|reduces?\s+to|means|gives|shows|"
        r"proves|implies|yields|equals|becomes)\b)",
        phrase,
    )
    if planner_tail is not None:
        tail = phrase[planner_tail.end() :].strip()
        if any(sym in tail for sym in _LEAN_LINE_MARKERS):
            return True
    discourse_prefixed_tail = re.match(
        r"(?is)^(?:(?:remaining|current|target|the|this)\s+){1,3}"
        r"(?:goals?|targets?|subgoals?|claims?)\s+",
        phrase,
    )
    if discourse_prefixed_tail is not None:
        tail = phrase[discourse_prefixed_tail.end() :].strip()
        if any(sym in tail for sym in _LEAN_LINE_MARKERS):
            return True
    if re.match(
        r"(?i)^(?:remaining\s+goal|current\s+goal|target\s+goal|the\s+goal|this\s+goal)\s+"
        r"(?:is|are|remains?|means|gives|shows|proves|implies|yields|equals)\b",
        stripped,
    ):
        return True
    tokens = _LEAN_ATOM_TOKEN_RE.findall(stripped)
    return bool(
        len(tokens) >= 2
        and _layout_local_let_lower_token_looks_like_prose(tokens[0].lower())
        and tokens[1].lower() in _SYMBOLIC_PROSE_VERBS
    )


def _looks_like_reasoning_proof_or_prose_fragment(s: str) -> bool:
    stripped = str(s or "").strip()
    if not stripped:
        return False
    if _looks_like_reasoning_symbolic_prose_fragment(stripped):
        return True
    if _looks_like_orphan_subgoal_proof_line(stripped):
        return True
    if _looks_like_tactic_proof_continuation_line(stripped):
        return not (
            stripped.startswith(("let ", "letI "))
            and _looks_like_top_level_let_expression(stripped)
            and not _json_subgoal_statement_is_proof_fragment(stripped)
        )
    proof_assign = r"[\s\S]*:=\s*(?:by\b|rfl\b|trivial\b|exact\b|simp\b|simpa\b)"
    if re.match(rf"^(?:have|haveI|suffices)\b{proof_assign}", stripped):
        return True
    if re.match(rf"^(?:let|letI)\b{proof_assign}", stripped):
        return _json_subgoal_statement_is_proof_fragment(stripped)
    return False


def _standalone_multiline_layout_subgoal_from_reasoning(
    reasoning_text: str,
) -> Optional[str]:
    raw_lines = [line.rstrip() for line in str(reasoning_text or "").splitlines()]
    nonempty_indices = [idx for idx, line in enumerate(raw_lines) if line.strip()]
    if not nonempty_indices:
        return None
    if re.match(r"(?s)^([-*]|\d+[.)])\s+", raw_lines[nonempty_indices[0]].strip()):
        return None
    candidate_lines = raw_lines[nonempty_indices[0] : nonempty_indices[-1] + 1]
    content_lines = [line for line in candidate_lines if line.strip()]
    if len(content_lines) < 2:
        return None
    if any(_looks_like_serialized_data_line(line.strip()) for line in content_lines):
        return None
    if not any(
        _line_has_layout_local_let_without_body(line.strip())
        for line in content_lines[:-1]
    ):
        return None
    candidate = normalize_subgoal_statement("\n".join(candidate_lines))
    if "\n" not in candidate:
        return None
    if _json_subgoal_statement_is_proof_fragment(candidate):
        return None
    if _looks_like_subgoal_explanation_line(candidate):
        return None
    if not _looks_like_extractable_subgoal_type(candidate):
        return None
    return candidate


def _standalone_multiline_proof_tail_subgoal_from_reasoning(
    reasoning_text: str,
) -> Optional[str]:
    raw = str(reasoning_text or "").strip()
    if "\n" not in raw or ":=" not in raw:
        return None
    first_nonempty = next((line.strip() for line in raw.splitlines() if line.strip()), "")
    if re.match(
        r"(?is)^(?:explanation|because|why|note|notes|strategy|proof idea|proof|rationale|reason|comment)\s*:",
        first_nonempty,
    ):
        return None
    if re.match(r"(?s)^([-*]|\d+[.)])\s+", first_nonempty):
        return None
    if any(_looks_like_serialized_data_line(line.strip()) for line in raw.splitlines()):
        return None
    if any(
        _line_has_layout_local_let_without_body(line.strip())
        for line in raw.splitlines()
    ):
        return None
    if _json_subgoal_statement_is_proof_fragment(raw):
        return None
    candidate = normalize_subgoal_statement(raw)
    if candidate == raw:
        return None
    if not _looks_like_extractable_subgoal_type(candidate):
        return None
    if _json_subgoal_statement_is_proof_fragment(candidate):
        return None
    return candidate


def _reasoning_multiline_candidate_variants(reasoning_text: str) -> list[str]:
    raw = str(reasoning_text or "").strip()
    if not raw:
        return []
    variants: list[str] = []
    seen: set[str] = set()

    def add(candidate: str) -> None:
        text = str(candidate or "").strip()
        if text and text not in seen:
            seen.add(text)
            variants.append(text)

    add(raw)
    queue = [raw]
    while queue:
        current = queue.pop(0)
        lines = current.splitlines()
        nonempty = next((idx for idx, line in enumerate(lines) if line.strip()), None)
        if nonempty is None:
            continue
        first = lines[nonempty].strip()
        stripped_label = False
        label = re.match(
            r"(?is)^(explanation|because|why|note|notes|strategy|proof idea|proof|rationale|reason|comment|subgoal)\s*:",
            first,
        )
        if label and label.group(1).lower() != "subgoal" and ":" in first:
            label_tail = first.split(":", 1)[1].strip()
            replacement = lines[:nonempty]
            if label_tail:
                replacement.append(label_tail)
            replacement.extend(lines[nonempty + 1 :])
            candidate = "\n".join(replacement).strip()
            if candidate and candidate not in seen:
                add(candidate)
                queue.append(candidate)
            stripped_label = True
        m_bullet = re.match(r"(?s)^([-*]|\d+[.)])\s+([\s\S]*)$", first)
        if m_bullet:
            replacement = lines[:nonempty]
            replacement.append(m_bullet.group(2).rstrip())
            dedent_continuations = any(
                rest.startswith("    ") for rest in lines[nonempty + 1 :] if rest.strip()
            )
            for rest in lines[nonempty + 1 :]:
                replacement.append(
                    rest[2:]
                    if dedent_continuations and rest.startswith("  ")
                    else rest
                )
            candidate = "\n".join(replacement).strip()
            if candidate and candidate not in seen:
                add(candidate)
                queue.append(candidate)
        if not stripped_label and not m_bullet:
            continue
    return variants


def extract_subgoals_from_reasoning(reasoning_text: str) -> list[str]:
    """Best-effort extraction of Lean types from chain-of-thought reasoning.

    Reasoning models (e.g. deepseek-reasoner) put chain-of-thought in
    ``reasoning_content`` while the structured answer goes in ``content``.
    When ``content`` is empty, this function mines the reasoning for
    embedded Lean type expressions — SUBGOAL: markers, backtick-quoted
    expressions, and high-density Lean lines.

    Applies a *stricter* bar than normal extraction to avoid false positives
    from verbose natural-language reasoning.
    """
    if not reasoning_text:
        return []
    for cand in extract_json_candidates(reasoning_text):
        try:
            data = json.loads(cand)
        except Exception:
            continue
        extracted = _extract_subgoals_from_json_payload(data)
        if extracted:
            return [x for x in extracted if x]
    if not re.search(r"\bSUBGOAL\s*:", reasoning_text):
        rendered = _extract_rendered_turnstile_subgoal_statements(reasoning_text)
        if rendered:
            return rendered
    if (
        "\n" in str(reasoning_text or "")
        and len(re.findall(r"\bSUBGOAL\s*:", str(reasoning_text or ""))) <= 1
        and _json_subgoal_statement_is_proof_fragment(reasoning_text)
    ):
        return []
    if re.search(r"\bSUBGOAL\s*:", reasoning_text):
        marked_results: list[str] = []
        seen_marked: set[str] = set()
        for candidate_text in _reasoning_multiline_candidate_variants(reasoning_text):
            if not re.search(r"\bSUBGOAL\s*:", candidate_text):
                continue
            marked = extract_subgoal_statements(candidate_text)
            if marked:
                for stmt in marked:
                    if stmt and stmt not in seen_marked:
                        seen_marked.add(stmt)
                        marked_results.append(stmt)
        if marked_results:
            return marked_results
        return []
    for candidate_text in _reasoning_multiline_candidate_variants(reasoning_text):
        standalone_proof_tail = _standalone_multiline_proof_tail_subgoal_from_reasoning(
            candidate_text
        )
        if standalone_proof_tail:
            return [standalone_proof_tail]
        standalone_layout = _standalone_multiline_layout_subgoal_from_reasoning(
            candidate_text
        )
        if standalone_layout:
            return [standalone_layout]
        candidate_first_line = next(
            (line.strip() for line in candidate_text.splitlines() if line.strip()),
            "",
        )
        if re.match(r"(?s)^([-*]|\d+[.)])\s+", candidate_first_line):
            continue
        if re.match(
            r"(?is)^(?:explanation|because|why|note|notes|strategy|proof idea|proof|rationale|reason|comment)\s*:",
            candidate_first_line,
        ):
            continue
        if not _json_subgoal_statement_is_proof_fragment(candidate_text):
            normalized_candidate = normalize_subgoal_statement(candidate_text)
            if (
                normalized_candidate != candidate_text
                and normalized_candidate
                and not _json_subgoal_statement_is_proof_fragment(
                    normalized_candidate
                )
                and not _looks_like_reasoning_proof_or_prose_fragment(
                    normalized_candidate
                )
                and _looks_like_extractable_subgoal_type(normalized_candidate)
            ):
                return [normalized_candidate]
            if (
                candidate_text != str(reasoning_text or "").strip()
                and not _looks_like_subgoal_explanation_line(candidate_text)
                and not _looks_like_reasoning_proof_or_prose_fragment(candidate_text)
                and _looks_like_extractable_subgoal_type(candidate_text)
            ):
                return [normalized_candidate or candidate_text]
    lines = reasoning_text.splitlines()
    results: list[str] = []
    for ln in lines:
        ln = ln.strip()
        if not ln or len(ln) < 5:
            continue
        if _looks_like_serialized_data_line(ln):
            continue
        # 1. Explicit SUBGOAL: markers (model might echo the prompt format)
        m = re.match(r"^SUBGOAL\s*:\s*(.+)$", ln)
        if m:
            if _json_subgoal_statement_is_proof_fragment(m.group(1)):
                continue
            candidate = normalize_subgoal_statement(m.group(1))
            if (
                not _json_subgoal_statement_is_proof_fragment(candidate)
                and _looks_like_extractable_subgoal_type(candidate)
            ):
                results.append(candidate)
            continue
        m_bullet = re.match(r"(?s)^([-*]|\d+[.)])\s+([\s\S]*)$", ln)
        if m_bullet:
            inner = m_bullet.group(2)
            m_sub = re.match(r"(?s)^SUBGOAL\s*:\s*([\s\S]+)$", inner)
            if m_sub:
                inner = m_sub.group(1)
            if _json_subgoal_statement_is_proof_fragment(inner):
                continue
            if _looks_like_reasoning_proof_or_prose_fragment(inner):
                continue
            if _looks_like_subgoal_explanation_line(inner):
                continue
            candidate = normalize_subgoal_statement(inner)
            if (
                candidate
                and not _looks_like_subgoal_explanation_line(candidate)
                and not _looks_like_reasoning_proof_or_prose_fragment(candidate)
                and _looks_like_extractable_subgoal_type(candidate)
            ):
                results.append(candidate)
            continue
        # 2. Backtick-quoted Lean expressions: `∀ n : ℕ, n > 0 → ...`
        backtick_hit = False
        for bq in re.findall(r"`([^`]+)`", ln):
            if _looks_like_reasoning_proof_or_prose_fragment(bq):
                continue
            bq = normalize_subgoal_statement(bq)
            if (
                len(bq) > 10
                and not _looks_like_reasoning_proof_or_prose_fragment(bq)
                and _looks_like_lean_type(bq)
            ):
                results.append(bq)
                backtick_hit = True
        # 3. Lines that are *predominantly* Lean (high structural density).
        #    Skip if we already extracted from backticks on this line to
        #    avoid adding the NL-wrapped version of the same expression.
        if (
            not backtick_hit
            and not _json_subgoal_statement_is_proof_fragment(ln)
            and not _looks_like_reasoning_proof_or_prose_fragment(ln)
        ):
            candidate = normalize_subgoal_statement(ln)
            proof_tail_stripped = (
                candidate != ln and _looks_like_extractable_subgoal_type(candidate)
            )
            if proof_tail_stripped:
                results.append(candidate)
                continue
            if _looks_like_lean_type(ln):
                lean_heavy = sum(1 for c in ln if c in "∀∃→↔∧∨¬≤≥⊆∈∣:=") >= 3
                words = re.findall(r"[A-Za-z]{3,}", ln)
                if (
                    lean_heavy
                    and len(words) <= 8
                    and not _looks_like_reasoning_proof_or_prose_fragment(candidate)
                ):
                    results.append(candidate)
    # Deduplicate preserving order
    seen: set[str] = set()
    deduped: list[str] = []
    for s in results:
        if s not in seen:
            seen.add(s)
            deduped.append(s)
    return deduped


def _extract_rendered_turnstile_subgoal_statements(text: str) -> list[str]:
    payloads = _rendered_turnstile_target_payloads(text)
    if not payloads:
        return []
    out: list[str] = []
    seen: set[str] = set()
    for payload in payloads:
        if _has_hard_lowercase_subgoal_label_boundary(payload):
            continue
        stmt = normalize_subgoal_statement(payload)
        if (
            stmt
            and stmt.upper() != "NONE"
            and not _looks_like_serialized_data_line(stmt)
            and not _json_subgoal_statement_is_proof_fragment(stmt)
            and not _looks_like_subgoal_explanation_line(stmt)
            and not _looks_like_reasoning_proof_or_prose_fragment(stmt)
            and _looks_like_extractable_subgoal_type(stmt)
            and stmt not in seen
        ):
            seen.add(stmt)
            out.append(stmt)
    return out


_LINE_START_SUBGOAL_MARKER_RE = re.compile(
    r"(?im)^[ \t]*(?:(?:[-*]|\d+[.)])[ \t]+)?"
    r"(?:(?:explanation|because|why|note|notes|strategy|proof idea|proof|"
    r"rationale|reason|comment)\s*:\s*)*SUBGOAL\s*:"
)


def _extract_explicit_subgoal_marker_batch_statements(
    text: str,
) -> Optional[list[str]]:
    src = str(text or "").strip()
    matches = list(_LINE_START_SUBGOAL_MARKER_RE.finditer(src))
    if not matches:
        return None
    out: list[str] = []
    seen: set[str] = set()

    def add(stmt: str) -> None:
        normalized = str(stmt or "").strip()
        if normalized and normalized not in seen:
            seen.add(normalized)
            out.append(normalized)

    for idx, match in enumerate(matches):
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(src)
        payload = src[match.end() : end].strip()
        if not payload:
            continue
        if _has_hard_lowercase_subgoal_label_boundary(payload):
            return []
        if _marker_payload_has_invalid_prefix_before_turnstile(payload):
            continue
        rendered = _extract_rendered_turnstile_subgoal_statements(payload)
        if rendered:
            for stmt in rendered:
                add(stmt)
            continue
        if _json_subgoal_statement_is_proof_fragment(payload):
            continue
        nested = extract_subgoal_statements(payload) if "\n" in payload else []
        if nested:
            for stmt in nested:
                add(stmt)
            continue
        stmt = normalize_subgoal_statement(payload)
        if (
            stmt
            and stmt.upper() != "NONE"
            and not _looks_like_serialized_data_line(stmt)
            and not _json_subgoal_statement_is_proof_fragment(stmt)
            and not _looks_like_subgoal_explanation_line(stmt)
            and not _looks_like_reasoning_proof_or_prose_fragment(stmt)
            and _looks_like_extractable_subgoal_type(stmt)
        ):
            add(stmt)
    return out


def _marker_payload_has_invalid_prefix_before_turnstile(payload: str) -> bool:
    text = str(payload or "").strip()
    if "⊢" not in text:
        return False
    prefix = text.split("⊢", 1)[0].strip()
    if not prefix:
        return False
    for raw_line in prefix.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        for _ in range(8):
            previous = line
            marker = re.match(r"(?s)^([-*]|\d+[.)])\s+([\s\S]*)$", line)
            if marker:
                line = marker.group(2).strip()
            label = re.match(
                r"(?is)^(?:explanation|because|why|note|notes|strategy|proof idea|proof|rationale|reason|comment)\s*:\s*([\s\S]+)$",
                line,
            )
            if label:
                line = label.group(1).strip()
            if line == previous:
                break
        if _SUBGOAL_MARKER_INVALID_DECL_HEAD_RE.match(line):
            return True
        if re.match(
            r"^(?:let|letI)\b[\s\S]*:=\s*(?:by\b|rfl\b|trivial\b|exact\b|simp\b|simpa\b)",
            line,
        ):
            return True
        if _rendered_line_looks_like_goal_context(line):
            continue
        if _json_subgoal_statement_is_proof_fragment(line):
            return True
    return False


def extract_subgoal_statements(text: str) -> list[str]:
    """
    Parse planner outputs in a simple, robust format.
    Preferred format: one statement per line starting with `SUBGOAL:`.
    All extracted statements are filtered through ``_looks_like_lean_type``
    to reject natural-language strings.
    """
    s = extract_final_segment(strip_thoughts(text)).strip()
    if not s:
        return []
    if s.strip().upper() == "NONE":
        return []
    # Try JSON first (some models keep emitting JSON even in plain mode)
    for cand in extract_json_candidates(s):
        try:
            data = json.loads(cand)
        except Exception:
            continue
        extracted = _extract_subgoals_from_json_payload(data)
        if extracted:
            return [x for x in extracted if x]

    blocks = extract_code_fences(s)
    src = blocks[0] if blocks else s
    if _has_hard_lowercase_subgoal_label_boundary(src):
        return []
    has_explicit_subgoal_marker = bool(re.search(r"\bSUBGOAL\s*:", src))
    marker_batch = (
        _extract_explicit_subgoal_marker_batch_statements(src)
        if has_explicit_subgoal_marker and "⊢" in src
        else None
    )
    if marker_batch is not None:
        return marker_batch
    explicit_marker_payload = _subgoal_marker_payload_without_rendered_strip(src)
    if explicit_marker_payload and "⊢" in explicit_marker_payload:
        rendered = _extract_rendered_turnstile_subgoal_statements(
            explicit_marker_payload
        )
        if rendered:
            return rendered
    if not has_explicit_subgoal_marker:
        rendered = _extract_rendered_turnstile_subgoal_statements(src)
        if rendered:
            return rendered
    payload_src = _json_subgoal_statement_payload(src)
    if payload_src != src and len(re.findall(r"\bSUBGOAL\s*:", src)) <= 1:
        if _json_subgoal_statement_is_proof_fragment(src):
            return []
        if "\n" in payload_src:
            nested = extract_subgoal_statements(payload_src)
            if nested:
                return nested
        for candidate_text in _reasoning_multiline_candidate_variants(payload_src):
            standalone_layout = _standalone_multiline_layout_subgoal_from_reasoning(
                candidate_text
            )
            if standalone_layout:
                return [standalone_layout]
        stmt = normalize_subgoal_statement(payload_src)
        if (
            stmt
            and stmt.upper() != "NONE"
            and not _looks_like_serialized_data_line(stmt)
            and not _json_subgoal_statement_is_proof_fragment(stmt)
            and not _looks_like_subgoal_explanation_line(stmt)
            and not _looks_like_reasoning_proof_or_prose_fragment(stmt)
            and _looks_like_extractable_subgoal_type(stmt)
        ):
            return [stmt]
        return []
    if "\n" in src and not has_explicit_subgoal_marker:
        for candidate_text in _reasoning_multiline_candidate_variants(src):
            candidate_first_line = next(
                (line.strip() for line in candidate_text.splitlines() if line.strip()),
                "",
            )
            if candidate_first_line.rstrip().endswith(
                (",", "→", "->", "↔", "<->", "∧", "∨", ":", ":=")
            ):
                continue
            standalone_layout = _standalone_multiline_layout_subgoal_from_reasoning(
                candidate_text
            )
            if standalone_layout:
                return [standalone_layout]

    # Pre-join indented continuation lines.  A line is considered a
    # continuation when (a) it is indented (leading whitespace) and
    # (b) the previous non-empty line ends with a trailing operator that
    # signals an incomplete expression.
    _TRAILING_CONT = (",", "→", "↔", "∧", "∨", "(", "[", "{", ":", ":=", "where")
    raw_lines = src.splitlines()
    joined: list[str] = []
    for raw_line in raw_lines:
        original_raw_line = raw_line
        stripped = raw_line.strip()
        if re.search(r"\bSUBGOAL\s*:", stripped):
            payload = _json_subgoal_statement_payload(stripped)
            if payload != stripped:
                leading = original_raw_line[
                    : len(original_raw_line) - len(original_raw_line.lstrip(" \t"))
                ]
                raw_line = leading + "SUBGOAL: " + payload
                stripped = raw_line.strip()
        label = re.match(
            r"(?is)^(?:explanation|because|why|note|notes|strategy|proof idea|proof|rationale|reason|comment)\s*:\s*([\s\S]+)$",
            stripped,
        )
        if label and re.search(r"\bSUBGOAL\s*:", label.group(1)):
            leading = original_raw_line[: len(original_raw_line) - len(original_raw_line.lstrip(" \t"))]
            raw_line = leading + label.group(1).strip()
            stripped = raw_line.strip()
        if not stripped:
            if joined and _line_has_layout_local_let_without_body(joined[-1]):
                joined[-1] = joined[-1].rstrip(" \t") + "\n"
                continue
            joined.append("")
            continue
        is_indented = len(raw_line) > 0 and raw_line[0] in (" ", "\t")
        prev_trailing = (
            joined
            and joined[-1]
            and any(joined[-1].rstrip().endswith(t) for t in _TRAILING_CONT)
        )
        prev_layout_let = bool(
            joined and joined[-1] and _line_has_layout_local_let_without_body(joined[-1])
        )
        starts_new_item = bool(
            re.match(r"^(?:SUBGOAL\s*:|[-*]\s+|\d+[.)]\s+)", stripped)
        )
        prev_layout_has_body = bool(
            prev_layout_let and _layout_local_let_has_body(joined[-1])
        )
        prev_open_proof_tail = bool(
            joined and joined[-1] and _line_ends_with_open_proof_tail(joined[-1])
        )
        prev_declaration_proof_tail = bool(
            joined
            and joined[-1]
            and re.search(r":=\s*by\b", joined[-1], flags=re.DOTALL)
        )
        proof_assignment_continuation = bool(joined and stripped.startswith(":="))
        proof_assignment_rhs_continuation = bool(
            joined
            and joined[-1].rstrip().endswith(":=")
            and re.match(
                r"^(?:by\b|rfl\b|trivial\b|exact\b|simp\b|simpa\b)",
                stripped,
            )
        )
        prev_layout_open_rhs = bool(
            prev_layout_let
            and not prev_layout_has_body
            and _layout_local_let_prefix_has_open_rhs(joined[-1])
        )
        body_like_layout_line = bool(
            prev_layout_let
            and (
                prev_layout_open_rhs
                or _layout_local_let_trailer_looks_like_body(joined[-1], stripped)
            )
        )
        symbolic_layout_prose = bool(
            prev_layout_let
            and _layout_local_let_trailer_looks_like_symbolic_prose(
                joined[-1], stripped
            )
        )
        unscoped_layout_prose = bool(
            prev_layout_let
            and _layout_local_let_trailer_looks_like_unscoped_prose_tail(
                joined[-1], stripped
            )
        )
        layout_term_continuation = bool(
            prev_layout_let
            and _layout_local_let_trailer_looks_like_term_continuation(
                joined[-1], stripped
            )
        )
        layout_argument_continuation = bool(
            prev_layout_let
            and _layout_local_let_trailer_looks_like_layout_argument_continuation(
                joined[-1], raw_line
            )
        )
        layout_continuation = layout_term_continuation or layout_argument_continuation
        if (
            prev_layout_has_body
            and (symbolic_layout_prose or unscoped_layout_prose)
            and not layout_continuation
            and not body_like_layout_line
        ):
            continue
        if (
            prev_layout_has_body
            and not prev_open_proof_tail
            and not starts_new_item
            and _looks_like_tactic_proof_continuation_line(stripped)
            and not layout_continuation
        ):
            continue
        if (
            (
                body_like_layout_line
                or layout_continuation
                or proof_assignment_rhs_continuation
                or not _looks_like_subgoal_explanation_line(stripped)
            )
            and (
                not symbolic_layout_prose
                or layout_continuation
                or body_like_layout_line
            )
            and (
                not unscoped_layout_prose
                or layout_continuation
                or body_like_layout_line
            )
            and not (
                prev_layout_has_body
                and _looks_like_orphan_subgoal_proof_line(stripped)
                and not prev_open_proof_tail
                and not layout_continuation
            )
            and (is_indented or (prev_layout_let and not starts_new_item))
        ) and (
            prev_trailing
            or prev_layout_let
            or prev_open_proof_tail
            or prev_declaration_proof_tail
            or proof_assignment_continuation
            or proof_assignment_rhs_continuation
        ):
            separator = "\n" if prev_layout_let else " "
            continuation = raw_line.rstrip() if prev_layout_let else stripped
            base = joined[-1].rstrip(" \t") if prev_layout_let else joined[-1].rstrip()
            joined[-1] = base + separator + continuation
        else:
            joined.append(stripped)

    out: list[str] = []
    for ln in joined:
        if not ln:
            continue
        if ln.upper() == "NONE":
            continue
        if _looks_like_subgoal_explanation_line(ln):
            continue
        if _looks_like_orphan_subgoal_proof_line(ln):
            continue
        if _looks_like_serialized_data_line(ln):
            continue
        m = re.match(r"(?s)^SUBGOAL\s*:\s*([\s\S]+)$", ln)
        if m:
            if _json_subgoal_statement_is_proof_fragment(m.group(1)):
                continue
            stmt = normalize_subgoal_statement(m.group(1))
            if (
                stmt
                and stmt.upper() != "NONE"
                and not _looks_like_serialized_data_line(stmt)
                and not _json_subgoal_statement_is_proof_fragment(stmt)
                and _looks_like_extractable_subgoal_type(stmt)
            ):
                out.append(stmt)
            continue
        if has_explicit_subgoal_marker and "SUBGOAL" not in ln:
            continue
        # Fallback: accept bullet/numbered lines that look like Lean statements.
        m2 = re.match(r"(?s)^([-*]|\d+[.)])\s+([\s\S]*)$", ln)
        if m2:
            inner = m2.group(2)
            # Strip SUBGOAL: prefix that survived the bullet extraction.
            explicit_subgoal_marker = False
            m_sub = re.match(r"(?s)^SUBGOAL\s*:\s*([\s\S]+)$", inner)
            if m_sub:
                inner = m_sub.group(1)
                explicit_subgoal_marker = True
            if _json_subgoal_statement_is_proof_fragment(inner):
                continue
            if (
                not explicit_subgoal_marker
                and _looks_like_reasoning_proof_or_prose_fragment(inner)
            ):
                continue
            if _looks_like_subgoal_explanation_line(inner):
                continue
            cand = normalize_subgoal_statement(inner)
            if (
                cand
                and not _looks_like_serialized_data_line(cand)
                and not _looks_like_subgoal_explanation_line(cand)
                and (
                    explicit_subgoal_marker
                    or not _looks_like_reasoning_proof_or_prose_fragment(cand)
                )
                and _looks_like_extractable_subgoal_type(cand)
            ):
                out.append(cand)
            continue
        # Last resort: bare lines that look like Lean type expressions.
        # This catches output from reasoning models that don't follow
        # prefix conventions.  The gate is intentionally broad — the
        # _looks_like_lean_type check below filters NL.
        _LEAN_SIGS = ("∀", "∃", "→", "↔", "∧", "∨", "∈", "⊆", "≤", "≥", "∣", ":", "=")
        if any(sym in ln for sym in _LEAN_SIGS) and not ln.startswith(
            ("#", "//", "--")
        ):
            if _json_subgoal_statement_is_proof_fragment(ln):
                continue
            if _looks_like_reasoning_proof_or_prose_fragment(ln):
                continue
            cand = normalize_subgoal_statement(ln)
            proof_tail_stripped = cand != ln and _looks_like_extractable_subgoal_type(
                cand
            )
            if (
                (
                    proof_tail_stripped
                    or not _looks_like_reasoning_proof_or_prose_fragment(cand)
                )
                and _looks_like_extractable_subgoal_type(cand)
            ):
                out.append(cand)
    # de-dup preserving order
    seen = set()
    dedup: list[str] = []
    for stmt in out:
        if stmt in seen:
            continue
        seen.add(stmt)
        dedup.append(stmt)
    return dedup


_JACCARD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*|\d+|[∀∃→↔∧∨¬≤≥=<>∈ℤℕℝℚℂ]")


def _jaccard_tokenize(s: str) -> frozenset:
    """Tokenize a string for Jaccard similarity (cached-friendly return type)."""
    return frozenset(_JACCARD_RE.findall((s or "").lower()))


def jaccard_similarity(a: str, b: str) -> float:
    a_tokens = _jaccard_tokenize(a)
    b_tokens = _jaccard_tokenize(b)
    if not a_tokens or not b_tokens:
        return 0.0
    return len(a_tokens & b_tokens) / len(a_tokens | b_tokens)
