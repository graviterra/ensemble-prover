import { useEffect, useRef, useState } from "react";
import { failureText, fetchRun } from "../api";
import { LiveMathPanel } from "../components/LiveMathPanel";
import { MemoryPanel } from "../components/MemoryPanel";
import { ProofGraph } from "../components/ProofGraph";
import { StopDialog } from "../components/StopDialog";
import { PollingControls } from "../components/PollingControls";
import { NodeMathematics } from "../components/NodeMathematics";
import { markStopSent, wasStopSent } from "../storage";
import { startPolling } from "../polling";
import type { Polling } from "../polling";
import { sweepAttempt } from "../sweeps";
import type { Milestone, RunDetail } from "../types";
import { classify, collectNodes, formatElapsed, humanize, looksLikeLean, nodeRole, nodeWords, processWords, safeProse, spendLines } from "../words";

export function AttemptScreen({ id, onLibrary, expanded = false, paused: controlledPaused, onPauseChange, onRefreshLibrary }: {
  id: string; onLibrary: () => void; expanded?: boolean;
  paused?: boolean; onPauseChange?: (paused: boolean) => void; onRefreshLibrary?: () => void;
}) {
  const [loadedDetail, setLoadedDetail] = useState<{ id: string; value: RunDetail } | null>(null);
  const detail = loadedDetail?.id === id ? loadedDetail.value : null;
  const [error, setError] = useState("");
  const [loading, setLoading] = useState(true);
  const [lastUpdated, setLastUpdated] = useState<number | null>(null);
  const [refreshing, setRefreshing] = useState(true);
  const [localPaused, setLocalPaused] = useState(false);
  const paused = controlledPaused ?? localPaused;
  const pollingRef = useRef<Polling | null>(null);
  const pausedRef = useRef(paused);
  pausedRef.current = paused;
  const [eventQuery, setEventQuery] = useState("");
  const [eventScope, setEventScope] = useState("");
  const [selectedId, setSelectedId] = useState<string | null>(null);
  const [milestone, setMilestone] = useState<Milestone | null>(null);
  const [dialogOpen, setDialogOpen] = useState(false);
  const [stopSent, setStopSent] = useState(() => wasStopSent(id));
  const lock = useRef(false);
  const openGuard = useRef(false);
  const inspector = useRef<HTMLElement>(null);

  useEffect(() => {
    let cancelled = false;
    let initial = true;
    setLoading(true);
    setError("");
    setLastUpdated(null);
    setMilestone(null);
    const polling = startPolling(async (signal) => {
      setRefreshing(true);
      const first = initial;
      initial = false;
      try {
        const next = await fetchRun(id, signal);
        if (cancelled) return;
        setLoadedDetail({ id, value: next });
        setError("");
        setLastUpdated(Date.now());
      } catch (err) {
        if (!cancelled) setError(failureText(err, "The local service did not answer."));
      } finally {
        if (!cancelled && first) setLoading(false);
        if (!cancelled) setRefreshing(false);
      }
    }, 4000, { paused: pausedRef.current });
    pollingRef.current = polling;
    return () => { cancelled = true; polling.stop(); };
  }, [id]);
  useEffect(() => { pollingRef.current?.setPaused(paused); }, [paused]);

  const sweepProblem = sweepAttempt(id)?.problem;
  const problem = detail?.problem || sweepProblem;
  const nodes = detail ? collectNodes(detail).map((node) =>
    node.kind === "root" && node.label === "root" && !detail.problem && sweepProblem ? { ...node, label: sweepProblem } : node
  ) : [];
  useEffect(() => {
    const nextNodes = detail ? collectNodes(detail) : [];
    setSelectedId((current) => current && nextNodes.some((node) => node.id === current) ? current : nextNodes[0]?.id ?? null);
  }, [detail]);

  function openStop() {
    if (stopSent || lock.current || openGuard.current) return;
    openGuard.current = true;
    setDialogOpen(true);
  }
  function closeStop() { openGuard.current = false; setDialogOpen(false); }
  function selectNode(nodeId: string) {
    setSelectedId(nodeId); setMilestone(null);
    if (window.matchMedia?.("(max-width: 980px)").matches) requestAnimationFrame(() => {
      inspector.current?.focus({ preventScroll: true });
      inspector.current?.scrollIntoView?.({ block: "start" });
    });
  }

  const view = detail ? classify(detail) : null;
  const process = detail ? processWords(detail.process.status, detail.process.detail) : null;
  const selectedIndex = nodes.findIndex((node) => node.id === selectedId);
  const selected = nodes[selectedIndex];
  const role = selected?.kind ?? nodeRole(selectedIndex);
  const reading = selected ? nodeWords(selected.status, role) : null;
  const events = detail?.events ?? [];
  const scopes = [...new Set(events.map((event) => event.scope).filter(Boolean))].sort();
  const needle = eventQuery.trim().toLowerCase();
  const matchingEvents = events.filter((event) => (!eventScope || event.scope === eventScope)
    && (!needle || `${event.scope} ${event.kind} ${event.text}`.toLowerCase().includes(needle)));
  const latest = events[events.length - 1];
  const lastEventS = detail?.lastEventS ?? latest?.elapsedS;
  const milestones = detail?.milestones ?? [];
  const related = selected ? events.filter((event) => role === "root" ? event.scope === "problem" : event.text.includes(selected.label)).slice(-8) : [];
  const showFormalization = detail?.formalization.status && detail.formalization.status !== "unavailable";

  return (
    <article className="attempt">
      <header className="run-header">
        <div>
          <h1 className={problem && looksLikeLean(problem) ? "statement mono" : "statement"}>
            {problem || (loading ? "Reading this attempt…" : detail ? "Problem text not recorded" : "Attempt unavailable")}
          </h1>
          <p className="meta mono">{id}{detail?.kind ? ` · ${humanize(detail.kind)}` : ""}</p>
        </div>
        <div className="run-actions">
          {view ? <span className={`mark mark-${view.tone}`}>{view.mark}</span> : null}
          {stopSent ? <p role="status">An interrupt was sent. Another one will not be sent.</p> :
            <button type="button" className="button" onClick={openStop} disabled={loading || !detail}>Stop</button>}
          <button type="button" className="text-button" onClick={onLibrary}>All results</button>
        </div>
      </header>
      <PollingControls lastUpdated={lastUpdated} refreshing={refreshing} error={error} paused={paused}
        onPauseChange={(next) => { setLocalPaused(next); onPauseChange?.(next); }}
        onRefresh={() => { void pollingRef.current?.refresh(); onRefreshLibrary?.(); }} />
      {error ? <div className="notice" role="alert">{error} {detail ? "Showing the last successful read." : ""}</div> : null}
      <div className="run-facts">
        <span><strong>Selected:</strong> {milestone ? "milestone receipt" : selected?.label || "none"}</span>
        <span><strong>Last recorded event:</strong> {lastEventS != null ? formatElapsed(lastEventS) : "not reported"}</span>
        <span><strong>Export:</strong> {humanize(detail?.exportState || "not reported")}</span>
        <span className="meta">Current recorded proof state</span>
      </div>

      <LiveMathPanel value={detail?.liveMath} paused={paused} readFailed={!!error} />
      <MemoryPanel key={id} runId={id} value={detail?.liveMath?.memory} paused={paused} />

      <div className={`proof-workspace${expanded ? " is-expanded" : ""}`}>
        <section className="graph-section" aria-labelledby="graph-heading">
          <div className="section-title"><h2 id="graph-heading">{expanded ? "Graph & evidence" : "Focused proof graph"}</h2><span className="mark">Observed relationships · partial coverage</span></div>
          <ProofGraph nodes={nodes} selectedId={selectedId} onSelect={selectNode} expanded={expanded} />
          <p className="meta graph-note">The graph shows recorded helper support relationships. A helper does not establish the root theorem or a successful export.</p>
        </section>
        <aside className="evidence-inspector" aria-label="Selected evidence" ref={inspector} tabIndex={-1}>
          <p className="eyebrow">{milestone ? "Selected milestone" : "Selected evidence"}</p>
          {milestone ? <>
            <h2>{humanize(milestone.kind) || "Recorded event"}</h2>
            <p className="mono">{formatElapsed(milestone.elapsedS)}</p>
            <pre className="evidence-statement">{milestone.text}</pre>
            <p className="meta">This receipt describes the recorded event. The graph continues to show the current recorded state.</p>
            <button type="button" className="text-button" onClick={() => setMilestone(null)}>Return to selected node</button>
          </> : selected && reading ? <>
            <h2>{selected.label}</h2>
            <p className="meta mono">{role} · {humanize(selected.status) || "status unknown"}</p>
            <NodeMathematics evidence={detail?.nodeEvidence?.[selected.id]} />
            <span className={`mark mark-${reading.certificate ? "verified" : reading.progress ? "progress" : "plain"}`}>{humanize(selected.status) || "Unknown"}</span>
            <p className="meta evidence-explanation">{reading.text}</p>
            {selected.recordedAtS != null ? <p className="meta">Recorded at {formatElapsed(selected.recordedAtS)}</p> : null}
            <h3>Recorded supports</h3>
            {selected.supports?.length ? <ul className="support-list">{selected.supports.map((support) => {
              const node = nodes.find((item) => item.id === support);
              return node ? <li key={support}><button type="button" className="text-button mono" onClick={() => selectNode(support)}>{node.label}</button></li> : null;
            })}</ul> : <p className="meta">No support relationships were reported for this node.</p>}
            <h3>{role === "root" ? "Problem-scope events" : "Event text matches"}</h3>
            {role === "helper" ? <p className="meta">Text matches may include other scopes or similarly named helpers. They are not linked proof receipts.</p> : null}
            {related.length ? <ol className="receipt-list">{related.map((event, index) => <li key={index}><time>{formatElapsed(event.elapsedS)}</time><span><small className="meta">Scope: {event.scope || "not reported"}</small><br />{event.text}</span></li>)}</ol> : <p className="meta">No matching retained events.</p>}
          </> : <p className="meta">{loading ? "Reading evidence…" : "Select a node or milestone to inspect its evidence."}</p>}
        </aside>
      </div>

      <section className="timeline-section" aria-labelledby="milestones-heading">
        <div className="section-title"><h2 id="milestones-heading">Milestone timeline</h2><span className="meta">Recorded evidence, not a solve ETA</span></div>
        {milestones.length ? <ol className="milestone-timeline">{milestones.slice(-4).map((item, index) => <li key={index} className={`receipt-${item.kind}`}>
          <button type="button" onClick={() => setMilestone(item)} aria-pressed={milestone?.elapsedS === item.elapsedS && milestone.kind === item.kind && milestone.text === item.text}>
            <time>{formatElapsed(item.elapsedS)}</time><span>{item.text}</span><small>Inspect evidence →</small>
          </button>
        </li>)}</ol> : <p className="meta">No milestones have been recorded yet.</p>}
        {milestones.length > 4 ? <details className="earlier-milestones"><summary>Inspect {milestones.length - 4} earlier milestones</summary><ol className="receipt-list">
          {milestones.slice(0, -4).map((item, index) => <li key={index}><time>{formatElapsed(item.elapsedS)}</time><button type="button" className="text-button" onClick={() => setMilestone(item)}>{item.text}</button></li>)}
        </ol></details> : null}
      </section>

      <div className="activity-workspace">
        <section aria-labelledby="activity-heading">
          <div className="section-title"><h2 id="activity-heading">Activity</h2><span className="meta">Latest recorded work by role</span></div>
          <div className="activity-lanes">{detail?.lanes.map((lane) => <article className={`activity-lane lane-${lane.name}`} key={lane.name}>
            <div><h3>{humanize(lane.name)}</h3><span className="meta">{lane.count} events{lane.lastElapsedS != null ? ` · ${formatElapsed(lane.lastElapsedS)}` : ""}</span></div>
            <p>{lane.lastText || (lane.count ? "Event text was not recorded." : "No activity recorded")}</p>
          </article>)}</div>
          {detail && !detail.lanes.length ? <p className="meta">No activity lanes were returned.</p> : null}
          {events.length ? <details className="event-log" open={expanded}><summary>Recent event log · {events.length} retained events</summary>
            <div className="event-filters">
              <label className="field event-query"><span>Search retained events</span><input type="search" value={eventQuery} onChange={(event) => setEventQuery(event.target.value)} placeholder="Find a tactic, helper, or message" /></label>
              <label className="field"><span>Event scope</span><select value={eventScope} onChange={(event) => setEventScope(event.target.value)}>
                <option value="">All scopes</option>
                {eventScope && !scopes.includes(eventScope) ? <option value={eventScope}>{eventScope} (not retained)</option> : null}
                {scopes.map((scope) => <option key={scope} value={scope}>{scope}</option>)}
              </select></label>
              {eventQuery || eventScope ? <button type="button" className="text-button" onClick={() => { setEventQuery(""); setEventScope(""); }}>Clear event filters</button> : null}
            </div>
            <p className="meta retained-event-count">{matchingEvents.length} of {events.length} retained events</p>
            {matchingEvents.length ? <ol className="receipt-list">
              {matchingEvents.slice().reverse().map((event, index) => <li key={index}><time>{formatElapsed(event.elapsedS)}</time><span><small className="meta">{event.scope} · {event.kind}</small><br />{event.text}</span></li>)}
            </ol> : <p className="meta">No retained events match these filters.</p>}
            <p className="meta">Search covers the latest retained events, not the complete run history.</p>
          </details> : null}
        </section>
        <aside className="operations">
          <h2>Operations</h2>
          {process ? <p>{process.text}</p> : null}
          <h3>Accounted spend</h3>
          <ul className="spend-list">{spendLines(detail?.costFields ?? {}).map((line) => <li key={line}>{line}</li>)}</ul>
          <h3>Root and export</h3>
          <p>{detail?.rootStatus || "No root status reported."}</p>
          {detail && safeProse(detail.exportReason) ? <p className="meta">{safeProse(detail.exportReason)}</p> : null}
          <p className="meta">Child finalizations: {detail?.childRootFinalizations ?? "unknown"}. These do not certify the root theorem.</p>
          <p className="meta">Closing this page does not stop a run.</p>
        </aside>
      </div>

      {showFormalization && detail ? <section className="section formalization-panel" aria-labelledby="formalization-heading">
        <h2 id="formalization-heading">Formalization</h2>
        <p>{humanize(detail.formalization.status)}</p>
        <p className="meta">A translated and typechecked statement is an input to proof search, not a proof certificate.</p>
        {detail.formalization.statement ? <pre className="formalization-source">{detail.formalization.statement}</pre> : null}
        {safeProse(detail.formalization.message) ? <p>{safeProse(detail.formalization.message)}</p> : null}
        {detail.formalization.leanSource ? <details><summary>Lean source</summary><pre className="formalization-source">{detail.formalization.leanSource}</pre></details> : null}
        {detail.formalization.artifactFiles.length ? <><h3>Saved artifacts</h3><ul>{detail.formalization.artifactFiles.map((name) => <li key={name}>{name}</li>)}</ul></> : detail.formalization.leanFile ? <p>Saved artifact: {detail.formalization.leanFile}</p> : null}
      </section> : null}

      {dialogOpen ? <StopDialog runId={id} onDismiss={closeStop} onDispatch={() => { lock.current = true; }}
        onRelease={() => { lock.current = false; }} onSignalled={() => {
          lock.current = true; openGuard.current = false; setStopSent(true); setDialogOpen(false); markStopSent(id);
        }} /> : null}
    </article>
  );
}
