"""Public live focus derived exclusively from bounded recorded observations."""
from __future__ import annotations

import stat
import time
from typing import Any

from console.live_math import COSTLY_ACTION_SECONDS, number, text
from console.session import AttachedRun


def live_math_view(attached: AttachedRun, *, now: float | None = None) -> dict[str, Any]:
    state = attached.state
    live = state.live_math
    age = None
    try:
        info = (attached.run_dir / "turns.jsonl").lstat()
        if stat.S_ISREG(info.st_mode):
            age = max(0.0, (time.time() if now is None else now) - info.st_mtime)
    except OSError:
        pass
    deferrals = [
        {"action": text(key[1], 120), "scope": text(value.get("scope"), 120),
         "reason": text(value.get("reason"), 80), "elapsedS": number(value.get("elapsed_s"))}
        for key, value in list(state.deferred.items())[-8:]
    ]
    inference_progress = []
    for observation in live.inference_progress.values():
        observed_at = number(observation.get("elapsedS"))
        # Combine recorded run-time age with silence since the latest trace
        # write. Another busy role must not make an old observation look fresh.
        observation_age = (
            max(0.0, state.last_elapsed_s - observed_at) + age
            if observed_at is not None and age is not None else None
        )
        inference_progress.append({
            **observation, "observationAgeS": observation_age,
            "stale": observation_age is not None and observation_age > 120,
        })
    source = live.source
    if not live.startup_seen and attached.tailer.generation == 0 and not source.get("available"):
        source = attached.summary.extra.get("source") or source
    return {
        "selection": dict(live.selection), "activity": dict(live.activity),
        "lastCostlyAction": dict(live.last_costly),
        "costlyActionThresholdS": COSTLY_ACTION_SECONDS,
        "source": dict(source), "settings": [dict(value) for value in live.settings.values()],
        "health": {
            "activeDeferrals": deferrals,
            "omittedDeferrals": max(0, len(state.deferred) - len(deferrals)) + state.deferred_overflow,
            "providerIssues": [dict(value) for value in live.provider_issues.values()],
            "inferenceProgress": inference_progress,
            "backlog": attached.backlog, "partialTrace": attached.partial_trace,
            "traceAvailable": attached.trace_available,
            "traceAgeS": age, "stale": age is not None and age > 120,
            "processStatus": text(attached.liveness.status, 80),
        },
    }
