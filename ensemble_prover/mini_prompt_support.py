"""Minimal prompt helpers used by Mini's formal-state search and retrieval."""

from __future__ import annotations


__all__ = ["STEERING_DIRECTIVE", "tactic_gen_multi_messages"]


STEERING_DIRECTIVE = (
    "Track dependency structure internally before constructing the answer. "
    "Output only the requested formal artifact or section; do not add "
    "explanatory prefaces or scratch reasoning.\n\n"
)


def tactic_gen_multi_messages(
    statement: str,
    current_goals: list[object],
    tactics_so_far: tuple[str, ...],
    *,
    num_candidates: int = 5,
    context_lemmas: str = "",
) -> list[dict[str, str]]:
    """Build Mini's ranked next-tactic prompt from the current Lean state."""

    system = (
        STEERING_DIRECTIVE
        + "You are a Lean tactic advisor. Given a proof state, suggest multiple "
        f"candidate next tactics ranked by likelihood of making progress.\n"
        "\n"
        "Rules:\n"
        f"- Output exactly {num_candidates} tactics, one per line.\n"
        "- Each line format: TACTIC: <lean_tactic> CONFIDENCE: <0.0-1.0>\n"
        "- Do NOT output `by`, just the tactic itself.\n"
        "- Do NOT use `sorry` or `admit`.\n"
        "- If the goal starts with ∀ or →, you MUST use `intro` or `intros` "
        "to bring variables into scope before referencing them. "
        "Only use identifiers that appear in the hypotheses list.\n"
        "- Rank by likelihood of closing goals or making progress.\n"
        "- Include diverse strategies (don't suggest 5 variants of simp).\n"
    )
    if context_lemmas.strip() and context_lemmas.strip() != "(none)":
        system += "- You may reference lemmas from the available context below.\n"

    goal_blocks: list[str] = []
    for index, goal in enumerate(current_goals):
        hypotheses = getattr(goal, "hypotheses", [])
        target = getattr(goal, "target", str(goal))
        block = f"Goal {index + 1}:"
        for hypothesis in hypotheses:
            block += f"\n    {hypothesis}"
        block += f"\n    ⊢ {target}"
        goal_blocks.append(block)
    goals_text = "\n".join(goal_blocks) if goal_blocks else "  (no goals)"
    tactics_text = (
        "\n".join(f"  {tactic}" for tactic in tactics_so_far)
        if tactics_so_far
        else "  (none yet)"
    )

    user = f"Statement: {statement}\n\n"
    if context_lemmas.strip() and context_lemmas.strip() != "(none)":
        user += f"Available lemmas:\n{context_lemmas}\n\n"
    user += (
        f"Current proof state:\n{goals_text}\n\n"
        f"Tactics applied so far:\n{tactics_text}\n\n"
        f"Suggest {num_candidates} candidate next tactics:"
    )
    return [
        {"role": "system", "content": system},
        {"role": "user", "content": user},
    ]
