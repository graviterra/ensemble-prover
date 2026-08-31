"""Lean failure analysis and model-facing rejection feedback."""

from __future__ import annotations

import re
from typing import Any, Dict, List, Optional, Tuple

from .lean_parser import (
    canonical_error_type,
    diagnostic_preview,
    fallback_error_type_from_text,
)
from .mini_coercion_advisor import coercion_repair_actions
from .mini_policy import _format_repair_obligation_block
from .proof_dossier import (
    _prompt_safe_inline_text,
    _prompt_safe_lean_diagnostic_text,
)
from .theorem_project import decode_theorem_target_context


class FailureAnalyzer:
    """Build structured repair feedback from a rejected Lean check."""

    max_diagnostics = 3
    max_goals = 4
    max_hypotheses = 10

    def analyze(self, result: Any) -> Dict[str, Any]:
        parsed = getattr(result, "parsed", None)
        raw_output = str(getattr(result, "output", "") or "")
        generated_declaration_name = str(
            getattr(result, "generated_declaration_name", "") or ""
        ).strip()
        generated_check_wrapper_unknown = bool(
            parsed is not None
            and generated_declaration_name
            and str(
                getattr(parsed, "unknown_identifier_name", "") or ""
            ).strip()
            == generated_declaration_name
        )
        if parsed is not None and bool(getattr(parsed, "infra_failure", False)):
            error_type = "infra_failure"
        elif parsed is not None and self._safe_int(
            getattr(parsed, "sorry_count", 0)
        ) > 0:
            error_type = "sorry_used"
        else:
            try:
                error_type = canonical_error_type(parsed)
            except Exception:
                error_type = ""
        if not error_type:
            error_type = fallback_error_type_from_text(raw_output)
        error_type = self._demote_active_root_wrapper_unknown(parsed, error_type)
        error_type = self._demote_generated_check_wrapper_unknown(
            parsed,
            error_type,
            generated_check_wrapper_unknown=generated_check_wrapper_unknown,
        )

        remaining_goals = self._remaining_goals(parsed)
        unsolved_goal_count = (
            self._safe_int(getattr(parsed, "unsolved_goal_count", 0))
            if parsed is not None
            else 0
        )
        parsed_goal_count = (
            len(list(getattr(parsed, "remaining_goals", []) or []))
            if parsed is not None
            else 0
        )
        hidden_goal_count = max(
            0,
            (unsolved_goal_count or parsed_goal_count) - len(remaining_goals),
        )
        analysis: Dict[str, Any] = {
            "error_type": error_type or "lean_rejected",
            "has_structured_parse": parsed is not None,
            "diagnostics": self._diagnostics(
                parsed,
                error_type,
                suppressed_unknown_identifier=(
                    generated_declaration_name
                    if generated_check_wrapper_unknown
                    else ""
                ),
            ),
            "diagnostic_search_text": self._diagnostic_search_text(
                parsed,
                suppressed_unknown_identifier=(
                    generated_declaration_name
                    if generated_check_wrapper_unknown
                    else ""
                ),
            ),
            "details": (
                self._details(
                    parsed,
                    suppressed_unknown_identifier=(
                        generated_declaration_name
                        if generated_check_wrapper_unknown
                        else ""
                    ),
                )
                if parsed is not None
                else self._fallback_details(raw_output, error_type)
            ),
            "remaining_goals": remaining_goals,
            "unsolved_goal_count": unsolved_goal_count,
        }
        if hidden_goal_count:
            analysis["hidden_goal_count"] = hidden_goal_count
        if generated_check_wrapper_unknown:
            analysis["generated_check_wrapper_unknown"] = True
            analysis["generated_declaration_name"] = generated_declaration_name
        sorry_count = self._safe_int(getattr(parsed, "sorry_count", 0))
        if sorry_count > 0:
            analysis["sorry_count"] = sorry_count
        flags = self._flags(parsed)
        if flags:
            analysis["flags"] = flags

        if parsed is None:
            analysis["parse_note"] = (
                "structured Lean parse unavailable; raw output retained in "
                "run artifacts"
            )
        return analysis

    def format_feedback(
        self,
        analysis: Dict[str, Any],
        *,
        search_enabled: bool = True,
        check_enabled: bool = True,
        role: str = "prove",
        dossier: Optional[Any] = None,
    ) -> str:
        family = str(analysis.get("error_type") or "lean_rejected")
        lines = [
            "Lean rejected that proof. Use this structured feedback for the next repair attempt.",
            f"Primary error family: `{family}`",
        ]

        target_goal = self._repair_target_goal(analysis)
        if target_goal:
            lines.append("")
            lines.append("Repair target:")
            index = target_goal.get("index")
            target = _prompt_safe_lean_diagnostic_text(
                target_goal.get("target") or "(target unavailable)",
                limit=700,
            )
            prefix = f"- goal {index}" if index is not None else "- goal"
            lines.append(f"{prefix} target: `{target}`")
            direct_actions = self._direct_local_goal_actions(
                {"remaining_goals": [target_goal]}
            )
            for action in direct_actions:
                lines.append(f"  immediate repair: {action}")

        diagnostics = list(analysis.get("diagnostics") or [])
        if diagnostics:
            lines.append("")
            lines.append("Diagnostics:")
            for diag in diagnostics:
                location = self._location_label(diag)
                summary = _prompt_safe_lean_diagnostic_text(
                    diag.get("summary") or "(no summary)",
                    limit=320,
                )
                if location:
                    lines.append(
                        f"- {_prompt_safe_inline_text(location, limit=120)}: {summary}"
                    )
                else:
                    lines.append(f"- {summary}")

        details = dict(analysis.get("details") or {})
        if details:
            lines.append("")
            lines.append("Actionable details:")
            for label, key in (
                ("Unknown identifier", "unknown_identifier"),
                ("Unknown universe", "unknown_universe"),
                ("Expected type", "expected_type"),
                ("Actual type", "actual_type"),
                ("Missing instance", "missing_instance"),
                ("Failed tactic", "failed_tactic"),
                ("Unification failure", "unification_failure"),
            ):
                value = details.get(key)
                if value:
                    lines.append(
                        f"- {label}: `{_prompt_safe_lean_diagnostic_text(value, limit=240)}`"
                    )
                    # Fix 2 (2026-05-22): when the LLM cites a hallucinated
                    # mini_* helper, append the verified-helper inventory so
                    # the next turn can self-correct. Drives recovery from
                    # the 6× hallucinated `outer_tsum_eval_p3_c1_v1` cascade
                    # in putnam_1978_b2_20260522_082821 (run.log lines 1601,
                    # 1607, 1638, 1644, 1784, 1825).
                    if key == "unknown_identifier" and dossier is not None:
                        from .feedback import (
                            helper_inventory_hint_for_unknown_identifier,
                        )
                        hint = helper_inventory_hint_for_unknown_identifier(
                            str(value or ""), dossier
                        )
                        if hint:
                            for hint_line in hint.split("\n"):
                                lines.append(f"  {hint_line}")
            suggestions = list(details.get("suggestions") or [])
            for suggestion in suggestions:
                lines.append(
                    "- Lean suggestion: "
                    f"`{_prompt_safe_lean_diagnostic_text(suggestion, limit=240)}`"
                )

        lines.extend(_format_repair_obligation_block(analysis))

        goals = list(analysis.get("remaining_goals") or [])
        unsolved_count = int(analysis.get("unsolved_goal_count") or 0)
        if goals or unsolved_count:
            lines.append("")
            count_label = (
                f"{unsolved_count} reported"
                if unsolved_count
                else f"{len(goals)} shown"
            )
            lines.append(f"Remaining goals ({count_label}):")
            for goal in goals:
                index = goal.get("index")
                target = _prompt_safe_lean_diagnostic_text(
                    goal.get("target") or "(target unavailable)",
                    limit=700,
                )
                prefix = f"- goal {index}" if index is not None else "- goal"
                lines.append(f"{prefix} target: `{target}`")
                hypotheses = list(goal.get("hypotheses") or [])
                if hypotheses:
                    rendered_hypotheses = "; ".join(
                        f"`{_prompt_safe_lean_diagnostic_text(h, limit=180)}`"
                        for h in hypotheses
                    )
                    lines.append(f"  hypotheses: {rendered_hypotheses}")
            hidden_goal_count = int(analysis.get("hidden_goal_count") or 0)
            if hidden_goal_count:
                lines.append(
                    f"- {hidden_goal_count} additional goal(s) were not shown; "
                    "repair the displayed blocker without assuming the proof is complete."
                )

        actions = self._repair_actions(
            analysis,
            search_enabled=search_enabled,
            check_enabled=check_enabled,
            role=role,
        )
        if actions:
            lines.append("")
            lines.append("Repair direction:")
            for action in actions:
                lines.append(f"- {action}")

        parse_note = analysis.get("parse_note")
        if parse_note:
            lines.append("")
            lines.append(f"Parser note: {parse_note}.")

        lines.append("")
        lines.append("Repair contract:")
        # B7 STRUCTURAL FIX (2026-05-18 audit): the "Repair delta:" prompt
        # instruction was prompt theater — zero parsers, zero gates, zero
        # metrics consumed it. Removed to avoid promising enforced behavior
        # the orchestrator does not actually enforce. The remaining rules
        # (material change, try_lean self-check, exact <hyp> for direct
        # closes) DO have backing enforcement gates.
        lines.append(
            "- The next Lean block must materially change the failed step; do not retry the same tactic, rewrite set, or lemma on the same target."
        )
        if check_enabled:
            lines.append(
                "- If `try_lean` is available in the next turn, call it on the revised proof body before submitting. Use `check_lean` only for declaration names/signatures; it does not check proof bodies."
            )
        lines.append(
            "- If the repair direction says a goal is already a hypothesis, close that subgoal with `exact <hyp>` before adding new rewrites or searches."
        )
        return "\n".join(lines)

    def _diagnostics(
        self,
        parsed: Any,
        error_type: str,
        *,
        suppressed_unknown_identifier: str = "",
    ) -> List[Dict[str, Any]]:
        if parsed is None:
            return []
        raw_diags = list(getattr(parsed, "diagnostics", []) or [])
        error_diags = [
            diag
            for diag in raw_diags
            if str(getattr(diag, "severity", "") or "").lower() == "error"
        ]
        selected = error_diags or raw_diags
        if self._is_active_root_wrapper_unknown(parsed):
            filtered = [
                diag
                for diag in selected
                if not self._diagnostic_is_active_root_wrapper_unknown(diag)
            ]
            if filtered:
                selected = filtered
        if suppressed_unknown_identifier:
            selected = [
                diag
                for diag in selected
                if not self._diagnostic_is_named_unknown(
                    diag,
                    suppressed_unknown_identifier,
                )
            ]
        out: List[Dict[str, Any]] = []
        for diag in selected[: self.max_diagnostics]:
            message = str(getattr(diag, "message", "") or "")
            summary = diagnostic_preview(message, canonical_error=error_type)
            if not summary:
                summary = str(getattr(diag, "summary", "") or "")
            item: Dict[str, Any] = {
                "severity": str(getattr(diag, "severity", "") or ""),
                "summary": self._compact(summary or message, limit=360),
                # Keep the full raw message alongside the (truncated) summary
                # so per-diagnostic rules can scan the full text without
                # falling back to the cross-boundary flat scan. (D4 fix.)
                "message": self._compact(message, limit=600),
            }
            for attr in ("line", "col"):
                value = getattr(diag, attr, None)
                if value is not None:
                    try:
                        item[attr] = int(value)
                    except Exception:
                        pass
            out.append(item)
        return out

    def _diagnostic_search_text(
        self,
        parsed: Any,
        *,
        suppressed_unknown_identifier: str = "",
    ) -> str:
        if parsed is None:
            return ""
        raw_diags = list(getattr(parsed, "diagnostics", []) or [])
        if suppressed_unknown_identifier:
            raw_diags = [
                diag
                for diag in raw_diags
                if not self._diagnostic_is_named_unknown(
                    diag,
                    suppressed_unknown_identifier,
                )
            ]
        messages = [
            self._compact(getattr(diag, "message", ""), limit=500)
            for diag in raw_diags[: self.max_diagnostics]
        ]
        return " ".join(message for message in messages if message)

    def _details(
        self,
        parsed: Any,
        *,
        suppressed_unknown_identifier: str = "",
    ) -> Dict[str, Any]:
        if parsed is None:
            return {}
        details: Dict[str, Any] = {}
        wrapper_unknown = self._is_active_root_wrapper_unknown(parsed)
        for key, limit in (
            ("unknown_identifier_name", 220),
            ("unknown_universe_name", 220),
            ("expected_type", 500),
            ("actual_type", 500),
            ("missing_instance", 420),
            ("failed_tactic", 260),
            ("unification_failure", 500),
        ):
            value = self._compact(getattr(parsed, key, None), limit=limit)
            if not value:
                continue
            out_key = key
            if key == "unknown_identifier_name":
                out_key = "unknown_identifier"
                if wrapper_unknown or value == suppressed_unknown_identifier:
                    continue
            elif key == "unknown_universe_name":
                out_key = "unknown_universe"
            details[out_key] = value

        suggestions = [
            self._compact(item, limit=280)
            for item in list(getattr(parsed, "suggestions", []) or [])[:3]
        ]
        suggestions = [item for item in suggestions if item]
        if suggestions:
            details["suggestions"] = suggestions
        return details

    def _is_active_root_wrapper_unknown(self, parsed: Any) -> bool:
        if parsed is None:
            return False
        name = str(getattr(parsed, "unknown_identifier_name", "") or "").strip()
        if name != "h_active":
            return False
        return any(
            bool(getattr(parsed, attr, None))
            for attr in (
                "missing_instance",
                "type_mismatch",
                "unification_failure",
                "binder_arity_mismatch",
                "tactic_failed",
                "parse_error",
            )
        )

    def _diagnostic_is_active_root_wrapper_unknown(self, diag: Any) -> bool:
        message = str(getattr(diag, "message", "") or "")
        return bool(
            re.search(
                r"\bUnknown identifier\b[^.\n`']*[`']?h_active[`']?",
                message,
                flags=re.IGNORECASE,
            )
        )

    def _diagnostic_is_named_unknown(self, diag: Any, name: str) -> bool:
        message = str(getattr(diag, "message", "") or "")
        clean_name = str(name or "").strip()
        if not message or not clean_name:
            return False
        return bool(
            re.search(r"\bUnknown (?:identifier|constant)\b", message, re.IGNORECASE)
            and re.search(
                rf"(?:[`']|\b){re.escape(clean_name)}(?:[`']|\b)",
                message,
            )
        )

    def _demote_generated_check_wrapper_unknown(
        self,
        parsed: Any,
        error_type: str,
        *,
        generated_check_wrapper_unknown: bool,
    ) -> str:
        if (
            str(error_type or "") != "unknown_identifier"
            or not generated_check_wrapper_unknown
        ):
            return error_type
        for attr, family in (
            ("missing_instance", "missing_instance"),
            ("type_mismatch", "type_mismatch"),
            ("unification_failure", "unification_failed"),
            ("binder_arity_mismatch", "binder_arity_mismatch"),
            ("tactic_failed", "tactic_failed"),
            ("parse_error", "parse_error"),
        ):
            if bool(getattr(parsed, attr, None)):
                return family
        return "lean_rejected"

    def _demote_active_root_wrapper_unknown(
        self,
        parsed: Any,
        error_type: str,
    ) -> str:
        if str(error_type or "") != "unknown_identifier":
            return error_type
        if not self._is_active_root_wrapper_unknown(parsed):
            return error_type
        for attr, family in (
            ("missing_instance", "missing_instance"),
            ("type_mismatch", "type_mismatch"),
            ("unification_failure", "unification_failed"),
            ("binder_arity_mismatch", "binder_arity_mismatch"),
            ("tactic_failed", "tactic_failed"),
            ("parse_error", "parse_error"),
        ):
            if bool(getattr(parsed, attr, None)):
                return family
        return error_type

    def _fallback_details(self, raw_output: str, error_type: str) -> Dict[str, Any]:
        details: Dict[str, Any] = {}
        if error_type == "unknown_identifier":
            match = re.search(
                r"unknown identifier\s+['`]?([^'`\s]+)['`]?",
                raw_output,
                flags=re.IGNORECASE,
            )
            if match:
                details["unknown_identifier"] = self._compact(
                    match.group(1),
                    limit=220,
                )
        return details

    def _remaining_goals(self, parsed: Any) -> List[Dict[str, Any]]:
        if parsed is None:
            return []
        goals = list(getattr(parsed, "remaining_goals", []) or [])
        out: List[Dict[str, Any]] = []
        for goal in goals[: self.max_goals]:
            item: Dict[str, Any] = {
                "target": self._compact(getattr(goal, "target", ""), limit=700),
            }
            index = getattr(goal, "index", None)
            if index is not None:
                try:
                    item["index"] = self._safe_int(index) + 1
                except Exception:
                    pass
            hypotheses = [
                self._compact(hyp, limit=180)
                for hyp in list(getattr(goal, "hypotheses", []) or [])[
                    : self.max_hypotheses
                ]
            ]
            hypotheses = [hyp for hyp in hypotheses if hyp]
            if hypotheses:
                item["hypotheses"] = hypotheses
            out.append(item)
        return out

    def _flags(self, parsed: Any) -> Dict[str, bool]:
        if parsed is None:
            return {}
        flags = {
            name: bool(getattr(parsed, name, False))
            for name in (
                "timeout",
                "infra_failure",
                "termination_failed",
                "parse_error",
                "unknown_identifier",
                "unknown_universe",
                "type_mismatch",
                "tactic_failed",
                "binder_arity_mismatch",
                "simp_no_progress",
                "proposition_falsified",
            )
        }
        if self._safe_int(getattr(parsed, "sorry_count", 0)) > 0:
            flags["sorry_used"] = True
        if getattr(parsed, "missing_instance", None):
            flags["missing_instance"] = True
        if getattr(parsed, "unification_failure", None):
            flags["unification_failed"] = True
        return {key: value for key, value in flags.items() if value}

    def _repair_actions(
        self,
        analysis: Dict[str, Any],
        *,
        search_enabled: bool,
        check_enabled: bool,
        role: str = "prove",
    ) -> List[str]:
        family = str(analysis.get("error_type") or "")
        details = dict(analysis.get("details") or {})
        actions: List[str] = []
        closed_numeric_actions = self._closed_numeric_goal_actions(analysis)
        actions.extend(self._direct_local_goal_actions(analysis))
        actions.extend(closed_numeric_actions)

        if bool(analysis.get("generated_check_wrapper_unknown")) and family == (
            "lean_rejected"
        ):
            actions.append(
                "The unknown name was the verifier's generated check wrapper, "
                "not a library declaration. Repair the submitted proof or an "
                "earlier diagnostic; do not search Mathlib for the wrapper."
            )
        elif family == "unknown_identifier":
            name = str(details.get("unknown_identifier") or "").strip()
            if name:
                safe_name = _prompt_safe_inline_text(name, limit=160)
                actions.append(
                    f"Do not cite `{safe_name}` again unless it is printed in the preamble, defined as a helper, or verified."
                )
            else:
                actions.append(
                    "Do not reuse unverified declaration names from this attempt."
                )
            actions.append(self._tool_action(search_enabled, check_enabled))
        elif family == "unknown_universe":
            actions.append(
                "Remove the invented universe/name or replace it with a printed declaration."
            )
        elif family == "parse_error":
            actions.append(
                "Repair Lean syntax first; submit a smaller proof block with balanced delimiters and valid tactic layout."
            )
        elif family == "type_mismatch":
            actions.append(
                "Align the term with the expected type before trying broader automation."
            )
            actions.append(self._tool_action(search_enabled, check_enabled))
        elif family == "missing_instance":
            actions.append(
                "Supply the missing instance explicitly, add the necessary typeclass hypothesis, or choose a lemma whose instance requirements match the context."
            )
        elif family == "unification_failed":
            actions.append(
                "Check binder order and implicit arguments; instantiate the lemma explicitly instead of relying on unification."
            )
        elif family == "proposition_falsified":
            actions.append(
                "The attempted witness or branch was refuted; re-derive that mathematical step rather than polishing the same tactic."
            )
        elif family == "binder_arity_mismatch":
            actions.append(
                "Match introductions/destructuring to the actual goal shape; inspect the first remaining target before introducing more variables."
            )
        elif family == "simp_no_progress":
            actions.append(
                "Do not retry the same `simp`; add the needed rewrite fact or switch to a more explicit proof step."
            )
        elif family in {"tactic_failed", "unsolved_goals"}:
            actions.append(
                "Focus on the first remaining goal target; prove a concrete intermediate `have` or choose a tactic tailored to that target."
            )
        elif family in {"timeout", "termination_failed"}:
            actions.append(
                "Avoid broad automation and recursive simplification; use shorter explicit steps or narrower rewrite sets."
            )
        elif family == "infra_failure":
            actions.append(
                "The verifier infrastructure failed before Lean gave a semantic proof error; retry the proof rather than treating this as a mathematical rejection."
            )
        elif family == "sorry_used":
            actions.append(
                "The MAIN proof path cannot contain `sorry`, `admit`, or "
                "placeholder holes. If a bridge lemma is missing, prove it, "
                "or pivot; do not emit an unproved local target, a helper "
                "stub, or absence-of-library prose."
            )
        elif family == "answer_safe_feedback_unavailable":
            actions.append(
                "Do not use `_solution` unfolding or non-visible reference values; revise using only the prompt-visible preamble and verified declarations."
            )
        else:
            actions.append(
                "Use the diagnostic location and first remaining target to make a specific proof change."
            )
        actions.extend(self._specialized_repair_actions(analysis))
        actions.extend(coercion_repair_actions(analysis))

        return [action for action in actions if action]

    def all_remaining_goals_are_direct_local_closes(
        self,
        analysis: Dict[str, Any],
    ) -> bool:
        goals = [
            goal
            for goal in list(analysis.get("remaining_goals") or [])
            if isinstance(goal, dict)
            and self._normalize_goal_for_match(goal.get("target"))
        ]
        if not goals or int(analysis.get("hidden_goal_count") or 0) > 0:
            return False
        return all(self._goal_has_direct_local_close(goal) for goal in goals)

    def _repair_target_goal(self, analysis: Dict[str, Any]) -> Dict[str, Any]:
        goals = [
            goal
            for goal in list(analysis.get("remaining_goals") or [])
            if isinstance(goal, dict)
        ]
        return dict(goals[0]) if goals else {}

    def _direct_local_goal_actions(self, analysis: Dict[str, Any]) -> List[str]:
        actions: List[str] = []
        seen: set[str] = set()
        for goal in list(analysis.get("remaining_goals") or []):
            if not isinstance(goal, dict):
                continue
            target = self._normalize_goal_for_match(goal.get("target"))
            if not target:
                continue
            index = goal.get("index")
            goal_label = f"Goal {index}" if index is not None else "This goal"
            for hyp in list(goal.get("hypotheses") or []):
                name, typ = self._split_local_hypothesis(str(hyp or ""))
                if not name or not typ:
                    continue
                if self._normalize_goal_for_match(typ) != target:
                    continue
                safe_name = _prompt_safe_inline_text(name, limit=120)
                if self._is_source_like_identifier(name) and safe_name == name:
                    action = (
                        f"{goal_label} is exactly hypothesis `{name}`; close that "
                        f"subgoal with `exact {name}`. Do not route this subgoal "
                        "through `simp` or `simpa`."
                    )
                else:
                    action = (
                        f"{goal_label} is already present as local hypothesis "
                        f"`{safe_name}`. Because that printed name may be inaccessible "
                        "source syntax, first bind it to a source-safe local name, "
                        "then close the subgoal with `exact`."
                    )
                if action not in seen:
                    seen.add(action)
                    actions.append(action)
                break
        return actions

    def _closed_numeric_goal_actions(self, analysis: Dict[str, Any]) -> List[str]:
        actions: List[str] = []
        goal = self._repair_target_goal(analysis)
        target = self._normalize_goal_for_match(goal.get("target"))
        if target and self._looks_like_closed_numeric_goal(target):
            index = goal.get("index")
            goal_label = f"Goal {index}" if index is not None else "The repair target"
            actions.append(
                f"{goal_label} is a closed numeric fact. Test a tiny proof such as `by native_decide`, `by decide`, or `by norm_num` before adding structural rewrites around it."
            )
        return actions

    def _split_local_hypothesis(self, hyp: str) -> Tuple[str, str]:
        text = " ".join(str(hyp or "").split())
        if ":" not in text:
            return "", ""
        name, typ = text.split(":", 1)
        name = name.strip()
        typ = typ.strip()
        if not name or " " in name:
            return "", ""
        return name, typ

    def _goal_has_direct_local_close(self, goal: Dict[str, Any]) -> bool:
        target = self._normalize_goal_for_match(goal.get("target"))
        if not target:
            return False
        for hyp in list(goal.get("hypotheses") or []):
            name, typ = self._split_local_hypothesis(str(hyp or ""))
            if name and self._normalize_goal_for_match(typ) == target:
                return True
        return False

    def _is_source_like_identifier(self, name: str) -> bool:
        return bool(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", str(name or "")))

    def _normalize_goal_for_match(self, value: Any) -> str:
        return " ".join(str(value or "").strip().split())

    def _looks_like_closed_numeric_goal(self, target: str) -> bool:
        if not re.search(r"=\s*-?\d+\b", target):
            return False
        if re.search(r"\b[a-zA-Z_][A-Za-z0-9_']*\b", target.replace("Nat.gcd", "")):
            # Permit namespace-qualified numeric functions below; reject
            # arbitrary local variables.
            allowed = {
                "Int",
                "Nat",
                "gcd",
                "lcm",
                "natAbs",
                "ofNat",
                "succ",
                "pred",
            }
            words = set(re.findall(r"\b[A-Za-z_][A-Za-z0-9_']*\b", target))
            if any(word not in allowed for word in words):
                return False
        return any(token in target for token in ("Nat.gcd", "Int.gcd", "gcd", "natAbs"))

    def _specialized_repair_actions(self, analysis: Dict[str, Any]) -> List[str]:
        """Return broad Lean/Mathlib repair hints keyed off recurring diagnostics.

        D4 fix (2026-05-08): scope each rule's conjunction to ONE
        diagnostic or to one explicit structured detail predicate. The
        previous implementation joined every analysis field into a single
        blob, so a rule like ``"nat.pow_pos" in lower and "function expected"
        in lower`` could fire when ``Nat.pow_pos`` appeared in one diagnostic
        or remaining goal and ``function expected`` came from a different
        diagnostic. Goal text is intentionally not conjoined with diagnostic
        predicates; it is already surfaced elsewhere in feedback.
        """

        actions: List[str] = []
        seen: set[str] = set()

        def emit(action: str) -> None:
            if action and action not in seen:
                seen.add(action)
                actions.append(action)

        details = dict(analysis.get("details") or {})
        detail_context = " ".join(
            str(value) for value in details.values() if value
        )
        detail_lower = detail_context.lower()

        diagnostics = [
            diag
            for diag in list(analysis.get("diagnostics") or [])
            if isinstance(diag, dict)
        ]
        # When no structured diagnostics are present, treat the legacy
        # ``diagnostic_search_text`` string plus parser details as a single
        # synthetic verifier message. That fallback is deliberately narrower
        # than the old flat scan: remaining-goal text is not folded in.
        scopes: List[Tuple[str, str]] = []
        if diagnostics:
            for diag in diagnostics:
                # Prefer the full raw message when present; fall back to
                # summary for older shapes.
                message = str(diag.get("message") or diag.get("summary") or "")
                if message:
                    scopes.append((message, message.lower()))
        else:
            legacy = str(analysis.get("diagnostic_search_text") or "")
            joined = (legacy + " " + detail_context).strip()
            if joined:
                scopes.append((joined, joined.lower()))

        expected_type = str(details.get("expected_type") or "")
        actual_type = str(details.get("actual_type") or "")
        if "∈ finset" in actual_type.lower() and "≠" in expected_type:
            emit(
                "You passed a membership proof where Lean expected a disequality proof. Re-check the lemma's explicit argument order with `#check @lemma_name`, use named arguments, or switch to a finite-sum proof that separates membership from the `i ≠ a` side condition."
            )

        for text, lower in scopes:
            if "nat.pow_pos" in lower and "function expected" in lower:
                emit(
                    "Do not apply `Nat.pow_pos h` to an extra `_`; in this Mathlib it already infers the exponent. Write `have hp : 0 < a ^ k := Nat.pow_pos h` or use `positivity`."
                )

            if "maximum recursion depth" in lower and "simp" in lower:
                emit(
                    "A broad `simp` recursed. Avoid `simp at *` or large `simp [f, ...]` over local finite-sum functions; rewrite the needed equality explicitly, then use a narrow `simpa [one_local_def, one_rewrite] using h`."
                )

            if (
                "type mismatch" in lower
                and "has type" in lower
                and "is expected to have type" in lower
                and re.search(
                    r"\b[A-Za-z_][A-Za-z0-9_'.]*\s*\([^)]*(?:\+|-)[^)]*\)",
                    text,
                )
            ):
                emit(
                    "When a type mismatch involves a function or indexed expression at a syntactically shifted term, instantiate the relevant hypothesis at the raw matching term before rewriting or normalizing. Keep those local instances explicit, then simplify with only the relevant local equalities."
                )

            if "∈ finset" in lower and "≠" in text:
                emit(
                    "You passed a membership proof where Lean expected a disequality proof. Re-check the lemma's explicit argument order with `#check @lemma_name`, use named arguments, or switch to a finite-sum proof that separates membership from the `i ≠ a` side condition."
                )

            if (
                "unexpected token 'in'" in lower
                or "unexpected token `in`" in lower
            ) and (
                "∑" in text
                or "addcommmonoid (sort" in lower
                or "∑" in detail_context
                or "addcommmonoid (sort" in detail_lower
            ):
                emit(
                    "Repair finite-sum syntax before proving content: prefer `∑ k in Finset.range n, f k` or `(Finset.range n).sum (fun k => f k)`. Avoid the membership-style binder `∑ k ∈ s, f k` unless you have verified that exact syntax in this context."
                )

        return actions

    def _analysis_search_text(self, analysis: Dict[str, Any]) -> str:
        parts: List[str] = [str(analysis.get("error_type") or "")]
        parts.append(str(analysis.get("diagnostic_search_text") or ""))
        details = dict(analysis.get("details") or {})
        parts.extend(str(value) for value in details.values() if value)
        for diag in list(analysis.get("diagnostics") or []):
            if isinstance(diag, dict):
                parts.append(str(diag.get("summary") or ""))
        for goal in list(analysis.get("remaining_goals") or []):
            if not isinstance(goal, dict):
                continue
            parts.append(str(goal.get("target") or ""))
            parts.extend(str(hyp) for hyp in list(goal.get("hypotheses") or []))
        return " ".join(parts)

    def _tool_action(self, search_enabled: bool, check_enabled: bool) -> str:
        if search_enabled and check_enabled:
            return (
                "Use `search_mathlib` to find replacement candidates, then `check_lean` to verify the exact name and signature before citing one."
            )
        if check_enabled:
            return (
                "Use `check_lean` to verify the exact name and signature before citing any replacement declaration."
            )
        if search_enabled:
            return (
                "Use `search_mathlib` for candidate names, then only cite a result whose displayed signature matches this goal."
            )
        return (
            "Only cite declarations printed in the preamble, standard syntax you know, or helpers you define in the same Lean block."
        )

    def _compact(self, value: Any, *, limit: int) -> str:
        text = " ".join(str(value or "").split())
        if limit > 0 and len(text) > limit:
            return text[: max(0, limit - 4)].rstrip() + " ..."
        return text

    def _safe_int(self, value: Any, default: int = 0) -> int:
        try:
            return int(value or 0)
        except Exception:
            return default

    def _location_label(self, diag: Dict[str, Any]) -> str:
        line = diag.get("line")
        col = diag.get("col")
        if line is None and col is None:
            return ""
        if line is not None and col is not None:
            return f"line {line}, col {col}"
        if line is not None:
            return f"line {line}"
        return f"col {col}"


_FAILURE_ANALYZER = FailureAnalyzer()


def _analyze_lean_failure(result: Any) -> Dict[str, Any]:
    return _FAILURE_ANALYZER.analyze(result)


def _format_lean_failure_feedback(
    analysis: Dict[str, Any],
    *,
    search_enabled: bool = True,
    check_enabled: bool = True,
    role: str = "prove",
    dossier: Optional[Any] = None,
) -> str:
    return _FAILURE_ANALYZER.format_feedback(
        analysis,
        search_enabled=search_enabled,
        check_enabled=check_enabled,
        role=role,
        dossier=dossier,
    )


def _lean_failure_all_goals_are_direct_local_closes(
    analysis: Dict[str, Any],
) -> bool:
    return _FAILURE_ANALYZER.all_remaining_goals_are_direct_local_closes(analysis)


def _prepend_repeated_failure_notice(
    feedback: str,
    conv: Any,
    analysis: Dict[str, Any],
) -> str:
    current_family, current_target = _failure_signature_from_analysis(analysis)
    if not current_family or not current_target:
        return feedback
    previous_family = ""
    previous_target = ""
    for msg in reversed(getattr(conv, "history", []) or []):
        if msg.get("role") != "user":
            continue
        previous_family, previous_target = _failure_signature_from_feedback(
            str(msg.get("content", "") or "")
        )
        if previous_family or previous_target:
            break
    if (
        previous_family == current_family
        and previous_target == current_target
    ):
        notice = (
            "Repeated Lean failure: the previous repair attempt left the same "
            f"`{current_family}` target `{current_target}`. Your next attempt "
            "must change the local proof shape for this target, not just restate "
            "the surrounding proof."
        )
        return notice + "\n\n" + feedback
    return feedback


def _failure_signature_from_analysis(
    analysis: Dict[str, Any],
) -> Tuple[str, str]:
    family = str(analysis.get("error_type") or "").strip()
    target = ""
    for goal in list(analysis.get("remaining_goals") or []):
        if isinstance(goal, dict):
            target = " ".join(str(goal.get("target", "") or "").split())
            if target:
                break
    return family, target


def _failure_signature_from_feedback(text: str) -> Tuple[str, str]:
    family_match = re.search(r"Primary error family:\s*`([^`]+)`", text or "")
    target_match = re.search(
        r"(?:Repair target:.*?- goal(?: \d+)? target:|goal\s+\d+\s+target:)\s*`([^`]+)`",
        text or "",
        flags=re.DOTALL,
    )
    family = family_match.group(1).strip() if family_match else ""
    target = " ".join(target_match.group(1).split()) if target_match else ""
    return family, target


def _needs_answer_safe_feedback_check(conv: Any) -> bool:
    """Whether to run the axiom-view (LLM-visible preamble) Lean recheck.

    The recheck serves two distinct purposes:
      1. Acceptance gating: require the proof to type-check against the
         answer-safe view too, blocking proofs that secretly relied on hidden
         filled-preamble values.
      2. Feedback sanitization (ALWAYS when preambles differ): render
         rejection diagnostics using the axiom view so reduced
         ``_solution`` values from ``lean_preamble`` never leak into
         the LLM's error messages, expected/actual types, or remaining
         goals.
    """
    if not bool(getattr(conv, "suppress_solution_placeholders", True)):
        return False
    prompt_preamble = (conv.preamble or "").strip()
    lean_preamble = (conv.lean_preamble or "").strip()
    lean_base = decode_theorem_target_context(lean_preamble)[0].strip()
    return bool(prompt_preamble and lean_base and prompt_preamble != lean_base)


def _manual_lean_failure_analysis(error_type: str, note: str) -> Dict[str, Any]:
    note_text = str(note or "").strip()
    return {
        "error_type": error_type,
        "analysis_source": "manual",
        "has_structured_parse": False,
        "diagnostics": (
            [
                {
                    "severity": "error",
                    "summary": note_text,
                    "message": note_text,
                }
            ]
            if note_text
            else []
        ),
        "diagnostic_search_text": note_text,
        "details": {},
        "remaining_goals": [],
        "unsolved_goal_count": 0,
        "parse_note": note_text,
    }


_RAW_FEEDBACK_MAX_CHARS = 8000


def _prompt_safe_raw_lean_output(raw: str, *, limit: int) -> str:
    """Preserve Lean's primary diagnostics under a char cap.

    The generic prompt snippet helper is intentionally tiny (10 lines), but
    raw-feedback mode exists specifically so the model can see the real Lean
    failure span and first remaining-goal block.
    """

    safe = _prompt_safe_lean_diagnostic_text(
        raw,
        limit=limit,
        preserve_line_breaks=True,
    )
    return safe or "(no output)"


def _format_raw_lean_feedback(feedback_result: Any) -> str:
    """Render sanitized Lean output as model-facing rejection feedback.

    Used by the A/B comparison path against the structured analyzer. We DO
    still respect the answer-safe gate by relying on whichever
    ``feedback_result`` the caller picked (full-check vs answer-safe
    recheck); this function never reaches into ``conv`` to grab the
    concrete-preamble result on its own.
    """
    raw = str(getattr(feedback_result, "output", "") or "").strip() or "(no output)"
    truncated = False
    if len(raw) > _RAW_FEEDBACK_MAX_CHARS:
        raw = raw[:_RAW_FEEDBACK_MAX_CHARS] + f"\n... ({len(raw) - _RAW_FEEDBACK_MAX_CHARS} more chars truncated)"
        truncated = True
    rendered = _prompt_safe_raw_lean_output(raw, limit=_RAW_FEEDBACK_MAX_CHARS)
    if truncated and "more chars truncated" not in rendered:
        rendered += "\n... (output truncated)"
    return (
        "Lean rejected that proof. The sanitized compiler output follows; read it "
        "carefully and change your next attempt accordingly. Do not repeat the "
        "rejected proof verbatim. If the output exposes a missing intermediate "
        "fact, local calculation, or bridge target, manufacture that fact in "
        "Lean with a proved local `have`/`suffices` or a fully proved helper "
        "in the same block. Treat missing non-Mathlib facts as proof "
        "obligations, not blockers.\n"
        "\n"
        "```\n"
        f"{rendered}\n"
        "```"
    )
