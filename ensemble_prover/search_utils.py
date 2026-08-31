"""Node identity, proof rendering, and MCTS scoring for tree search.

``search`` and ``tactic_tree`` share these dependency-light utilities for
building Lean tactic blocks and ranking proof-tree nodes.
"""

from __future__ import annotations

import math
import uuid
from typing import Sequence

from .math_utils import clamp_probability


def make_node_id() -> str:
    """Generate a short random node identifier."""
    return uuid.uuid4().hex[:12]


def tactics_to_proof(tactics: Sequence[str]) -> str:
    """Convert a tactic sequence to a Lean proof block.

    Accepts any sequence (list, tuple, etc.).  Returns ``"by sorry"``
    for an empty sequence.
    """
    if not tactics:
        return "by sorry"
    body = "\n".join(f"  {t}" for t in tactics)
    return f"by\n{body}"


class MCTSScoreMixin:
    """Mixin providing PUCT/UCB1 scoring for tree search nodes.

    Requires the host dataclass to define:
      - ``visits: int``
      - ``total_reward: float``
      - ``prior: float``
    """

    visits: int
    total_reward: float
    prior: float

    @property
    def q_value(self) -> float:
        if self.visits == 0:
            return 0.0
        try:
            value = float(self.total_reward) / self.visits
        except Exception:
            return 0.0
        return clamp_probability(value, default=0.0)

    def puct_score(self, parent_visits: int, c_puct: float = 1.4) -> float:
        """Compute PUCT (Predictor + UCT) score for MCTS selection.

        Uses the AlphaGo/AlphaZero formula:
        Q(s,a) + c_puct * P(s,a) * sqrt(N(s)) / (1 + N(s,a))
        where P(s,a) is the prior probability.
        """
        exploit = self.q_value
        prior = clamp_probability(self.prior, default=0.0)
        explore = c_puct * prior * math.sqrt(max(1, parent_visits)) / (1 + self.visits)
        if self.visits == 0:
            # Unvisited: guarantee visit before revisiting siblings, but let
            # prior break ties so high-probability candidates go first.
            return 1e9 + explore
        score = exploit + explore
        if not math.isfinite(score):
            return exploit
        return score

    def ucb1(self, parent_visits: int, c_puct: float = 1.4) -> float:
        """Backward-compatible alias for the PUCT selection score."""
        return self.puct_score(parent_visits, c_puct=c_puct)

    def backpropagate(self, reward: float) -> None:
        """Record a single simulation result on this node."""
        if not math.isfinite(float(self.total_reward)):
            self.total_reward = 0.0
        self.visits += 1
        self.total_reward += clamp_probability(reward, default=0.0)
