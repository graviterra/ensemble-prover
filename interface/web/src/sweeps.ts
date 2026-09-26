type SweepAttempt = {
  sweep: string;
  problem: string;
  problemIndex: number;
  attemptIndex: number;
  stage: number;
};

export function sweepAttempt(id: string): SweepAttempt | null {
  const match = /^sweeps\/([^/]+)\/attempts\/(\d+)_([^/]+)\/attempt_(\d+)(\.answer_preparation)?$/.exec(id);
  if (!match) return null;
  const problemIndex = Number(match[2]), attemptIndex = Number(match[4]);
  if (!Number.isSafeInteger(problemIndex) || !Number.isSafeInteger(attemptIndex)) return null;
  return { sweep: match[1], problem: match[3], problemIndex, attemptIndex, stage: match[5] ? 0 : 1 };
}

export function nextSweepRun(currentId: string, ids: string[]): string {
  let selectedId = currentId;
  let selected = sweepAttempt(currentId);
  if (!selected) return currentId;
  for (const id of ids) {
    const candidate = sweepAttempt(id);
    if (!candidate || candidate.sweep !== selected.sweep) continue;
    // Sweep ordinals describe sequence. Modification times also change when
    // completed results are exported and must not send the viewer backwards.
    const newerProblem = candidate.problemIndex > selected.problemIndex;
    const sameProblem = candidate.problemIndex === selected.problemIndex && candidate.problem === selected.problem;
    const newerAttempt = sameProblem && (candidate.attemptIndex > selected.attemptIndex ||
      (candidate.attemptIndex === selected.attemptIndex && candidate.stage > selected.stage));
    if (newerProblem || newerAttempt) { selectedId = id; selected = candidate; }
  }
  return selectedId;
}
