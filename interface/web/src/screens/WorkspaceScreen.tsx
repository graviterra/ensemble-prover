import { useEffect, useRef, useState } from "react";
import { fetchLibrary, failureText } from "../api";
import { startPolling } from "../polling";
import type { Polling } from "../polling";
import type { LibraryRun } from "../types";
import { timeValue } from "../words";
import { AttemptScreen } from "./AttemptScreen";
import { nextSweepRun, sweepAttempt } from "../sweeps";

export function WorkspaceScreen({ id, expanded, followSweep = true, onChoose, onOpen, onLibrary, onNew }: {
  id?: string; expanded: boolean; followSweep?: boolean; onChoose: (id: string) => void;
  onOpen: (id: string, follow?: boolean) => void; onLibrary: () => void; onNew: () => void;
}) {
  const [runs, setRuns] = useState<LibraryRun[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState("");
  const [paused, setPaused] = useState(false);
  const pausedRef = useRef(paused);
  pausedRef.current = paused;
  const pollingRef = useRef<Polling | null>(null);
  useEffect(() => {
    let active = true;
    const polling = startPolling(async (signal) => {
      try {
        const found = await fetchLibrary(signal);
        if (!active) return;
        found.sort((a, b) => timeValue(b.lastWriteTs) - timeValue(a.lastWriteTs));
        setRuns(found);
        setError("");
        if (!id) {
          const next = found.find((run) => run.launchStatus === "running") ?? found[0];
          if (next) onChoose(next.id);
        } else if (followSweep && !pausedRef.current) {
          const next = nextSweepRun(id, found.map((run) => run.id));
          if (next !== id) onChoose(next);
        }
      } catch (err) { if (active) setError(failureText(err)); }
      finally { if (active) setLoading(false); }
    }, 4000, { paused: pausedRef.current });
    pollingRef.current = polling;
    return () => { active = false; polling.stop(); };
  }, [id, followSweep, onChoose]);
  useEffect(() => { pollingRef.current?.setPaused(paused); }, [paused]);
  const sweep = id ? sweepAttempt(id) : null;
  return <>
    <div className="workspace-toolbar">
      <label className="run-selector"><span>Run</span><select aria-label="Choose run" value={id ?? ""} onChange={(event) => onOpen(event.target.value)}>
        {!id ? <option value="">Select a recorded run</option> : !runs.some((run) => run.id === id) ? <option value={id}>{id}</option> : null}
        {runs.map((run) => <option value={run.id} key={run.id}>{run.problem || sweepAttempt(run.id)?.problem || run.label || run.id} · {run.id}</option>)}
      </select></label>
      <button type="button" className="text-button" onClick={onNew}>Launch new run →</button>
    </div>
    {sweep && id ? <div className="sweep-follow">
      <label className="check"><input type="checkbox" checked={followSweep} onChange={(event) => onOpen(id, event.target.checked)} /><span>Follow sweep</span></label>
      <span className="meta mono">{sweep.sweep}</span>
      <span className="meta">{paused ? "Automatic updates and sweep following are paused." : followSweep ? "Advances to the next recorded attempt in this sweep." : "Pinned to this attempt."}</span>
    </div> : null}
    {id ? <AttemptScreen key={id} id={id} expanded={expanded} onLibrary={onLibrary}
      paused={paused} onPauseChange={setPaused} onRefreshLibrary={() => { void pollingRef.current?.refresh(); }} /> : <section className="workspace-empty">
      <p className="eyebrow">Proof workspace</p><h1>{loading ? "Reading recorded runs…" : "Choose a theorem to begin"}</h1>
      <p>The proof graph, selected evidence, milestones, and activity appear here as the run records them.</p>
      {error ? <p role="alert">{error}</p> : null}
      <div className="row-actions"><button type="button" className="button button-primary" onClick={onNew}>Open launcher</button><button type="button" className="button" onClick={onLibrary}>Browse results</button></div>
    </section>}
    {id && error ? <p role="alert" className="meta">Run list: {error}</p> : null}
  </>;
}
