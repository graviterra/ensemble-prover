import { useEffect, useId, useRef, useState } from "react";
import { failureText, fetchMemory, fetchMemoryRequests, fetchSession, materializeMemoryEvidence, submitMemoryRequest } from "../api";
import { refreshPausedPermissions } from "../memory";
import type { MemoryRequest, MemoryRow, MemoryView } from "../memory";
import "./memory.css";

const labels: Record<string, string> = { checked_solution: "Reported checked solution", checked_reduction: "Reported checked reduction", elaborated_closed: "Elaborated · acceptance pending", elaborated_partial: "Partial application", probe_rejected: "Attempted operation rejected", probe_inconclusive: "Inconclusive probe", not_checked: "Application not checked", unavailable: "Evidence unavailable" };
export function MemoryPanel({ runId, value, paused = false }: { runId: string; value?: MemoryView; paused?: boolean }) {
  const heading = useId();
  const [view, setView] = useState(value);
  const [now, setNow] = useState(Date.now());
  const [filter, setFilter] = useState("candidates");
  const [control, setControl] = useState(false);
  const [requests, setRequests] = useState<MemoryRequest[]>([]);
  const [note, setNote] = useState("");
  const [statement, setStatement] = useState("");
  const [seconds, setSeconds] = useState("10");
  const [message, setMessage] = useState("");
  const [busy, setBusy] = useState(false);
  const [artifacts, setArtifacts] = useState<Record<string, string>>({});
  const requestIntent = useRef<{ content: string; requestId: string } | null>(null);
  const pausedRef = useRef(paused);
  const activeMemory = !!value && value.mode !== "off";
  pausedRef.current = paused;
  useEffect(() => { if (!value || value.mode === "off" || !paused) setView(value); }, [value, paused]);
  useEffect(() => {
    const expiry = window.setInterval(() => setNow(Date.now()), 500);
    return () => window.clearInterval(expiry);
  }, []);
  useEffect(() => {
    if (!activeMemory) return;
    let closed = false;
    let inFlight = false;
    const abort = new AbortController();
    void fetchSession().then((session) => { if (!closed) setControl(session.control); }).catch(() => {});
    async function refresh() {
      if (inFlight) return;
      inFlight = true;
      try {
        const next = await fetchMemory(runId, abort.signal);
        if (!closed) setView((current) => !next || next.mode === "off" ? next : pausedRef.current ? refreshPausedPermissions(current, next) : next);
        if (!closed) {
          const currentRequests = await fetchMemoryRequests(runId, abort.signal);
          if (!closed) setRequests(currentRequests);
        }
      } catch { /* Existing lease expires locally; unavailable validation never renews it. */ }
      finally { inFlight = false; }
    }
    void refresh();
    const timer = window.setInterval(() => { setNow(Date.now()); void refresh(); }, 3000);
    return () => { closed = true; abort.abort(); window.clearInterval(timer); };
  }, [runId, activeMemory]);
  const eligible = !!view && activeMemory && view.mode !== "off" && view.eligibility_lease_until * 1000 > now && view.status !== "unavailable";
  const current = eligible ? view : undefined;
  const groups = ["candidates", "applications", "obstructions", "proposals", "notes"] as const;
  const rows = current?.[filter as typeof groups[number]] ?? [];
  async function command(kind: string, row?: MemoryRow) {
    if (!current || busy || !control) return;
    setBusy(true);
    const payload: Record<string, string | number> = { kind,
      goal_id: current.goal_id, environment_id: current.environment_id, policy_id: current.policy_id,
      candidate_id: row?.candidate_id || row?.id || "", allocation_id: kind === "generalization" ? current.research_allocation_id : current.allocation_id,
      retry_of: kind === "retry" ? row?.event_id || "" : "",
      max_seconds: kind === "retry" || kind === "generalization" ? Number(seconds) : 0,
      text: kind === "note" ? note : "", statement: kind === "generalization" ? statement : "" };
    const content = JSON.stringify(payload);
    if (requestIntent.current?.content !== content) requestIntent.current = { content, requestId: crypto.randomUUID() };
    payload.request_id = requestIntent.current.requestId;
    try {
      const result = await submitMemoryRequest(runId, payload);
      requestIntent.current = null;
      setRequests((items) => [...items, result].slice(-64));
      setMessage(`Request ${result.status}. A stored request awaits scheduler admission.`);
      if (kind === "note") setNote("");
    } catch (error) { setMessage(failureText(error, "The request could not be stored. Its execution is not established.")); }
    finally { setBusy(false); }
  }
  async function materialize(row: MemoryRow, digest = row.evidence_digest) {
    if (!current || busy || !control) return;
    setBusy(true);
    try {
      const artifactId = await materializeMemoryEvidence(runId, row.event_id, digest);
      if (artifactId) setArtifacts((items) => ({ ...items, [digest === row.evidence_digest ? row.event_id : `${row.event_id}:${digest}`]: artifactId }));
    } catch { setMessage("Evidence could not be copied under the current source policy."); }
    finally { setBusy(false); }
  }
  return <section className="memory-panel" aria-labelledby={heading}>
    <header className="section-title"><h2 id={heading}>Mathematical memory</h2><span className="mark mark-plain">{current?.mode || view?.mode || "off"} · recorded evidence</span></header>
    <p className="meta">Prior checked reports retain their original assumptions and environment. They require current verification before proof reuse.</p>
    {!current ? <p role="status">Memory evidence unavailable. Current eligibility could not be confirmed; restricted content is hidden.</p> : <>
      {paused ? <p className="meta">Observations paused. Permission checks continue.</p> : null}
      {current.partial ? <p className="meta">Coverage is partial{current.omitted != null ? `; ${current.omitted} records omitted` : ""}.</p> : null}
      <label className="field"><span>Memory records</span><select value={filter} onChange={(event) => setFilter(event.target.value)}>{groups.map((group) => <option key={group} value={group}>{group[0].toUpperCase() + group.slice(1)}</option>)}</select></label>
      {rows.length ? <div className="memory-cards">{rows.map((row, index) => <article key={`${row.event_id}-${index}`}>
        <h3>{row.name || ({ notes: "Recorded research note", proposals: "Generalization proposal", applications: "Application report", candidates: "Prior theorem candidate", obstructions: "Research obstruction" } as Record<string, string>)[filter] || "Research observation"}</h3>
        <span className="mark mark-plain">{labels[row.outcome] || "Research observation"}</span>
        <p className="meta">Scope: {row.scope || current.scope || "not recorded"} · {row.freshness || "historical report"}</p>
        {row.statement || row.text ? <pre tabIndex={0}>{row.statement || row.text}</pre> : <p>Formal statement not recorded.</p>}
        {row.statement_truncated ? <p className="meta">Statement preview truncated.</p> : null}
        {row.reason ? <p>{row.reason}</p> : null}
        {row.operation ? <p>Operation: {row.operation}{row.direction ? ` · ${row.direction}` : ""}</p> : null}
        {row.assumptions ? <p>Assumptions: {row.assumptions}</p> : null}
        {row.conditions ? <p>Unresolved conditions: {row.conditions}</p> : null}
        {row.remaining_goals.length ? <details><summary>Remaining obligations</summary>{row.remaining_goals.map((goal, i) => <pre key={i}>{goal}</pre>)}</details> : null}
        {row.retry_conditions ? <p>Retry conditions: {row.retry_conditions}</p> : null}
        {row.consumers.length ? <details><summary>Prior consumer examples</summary>{row.consumers.map((consumer, i) => <pre key={i}>{consumer}</pre>)}</details> : null}
        {([ ["instance_ids", "Reported source instance identifiers"], ["source_instances", "Reported source instances"], ["changed_assumptions", "Reported changed assumptions"], ["specialization_links", "Reported specialization links"], ["intended_consumers", "Intended consumers"] ] as const).map(([key, title]) => row[key].length ? <details key={key}><summary>{title}</summary>{row[key].map((item, i) => <pre key={i}>{item}</pre>)}</details> : null)}
        {row.expected_use || filter === "proposals" ? <p>Expected use: {row.expected_use || "Not recorded"}</p> : null}
        {row.observed_use || filter === "proposals" ? <p>Reported observed use: {row.observed_use || "Not recorded"}</p> : null}
        {row.artifact_available || artifacts[row.event_id] ? <a href={`/api/memory/${encodeURIComponent(runId)}/artifacts/${artifacts[row.event_id] || row.artifact_id}`} target="_blank" rel="noreferrer">Inspect evidence artifact</a> : control && row.evidence_digest ? <button type="button" disabled={busy} onClick={() => void materialize(row)}>Prepare evidence for inspection</button> : <p className="meta">Evidence artifact unavailable.</p>}
        {row.evidence_digests.filter((digest) => digest !== row.evidence_digest).map((digest, i) => artifacts[`${row.event_id}:${digest}`] ? <a key={digest} href={`/api/memory/${encodeURIComponent(runId)}/artifacts/${artifacts[`${row.event_id}:${digest}`]}`} target="_blank" rel="noreferrer">Inspect additional evidence {i + 2}</a> : control ? <button key={digest} type="button" disabled={busy} onClick={() => void materialize(row, digest)}>Prepare additional evidence {i + 2}</button> : null)}
        {control ? <div className="memory-actions"><button type="button" disabled={busy || !row.candidate_id && !row.id} onClick={() => void command("pin", row)}>Pin</button>{filter === "applications" ? <button type="button" disabled={busy || !row.event_id || !row.candidate_id || !row.operation || !current.allocation_id || !["assist", "develop"].includes(current.mode)} onClick={() => void command("retry", row)}>Request retry</button> : null}</div> : null}
      </article>)}</div> : <p>No eligible records in this view. Bounded retrieval does not establish that no relevant theorem exists.</p>}
      {control ? <div className="memory-notebook"><h3>Campaign notebook</h3><label className="field"><span>Research note</span><textarea maxLength={8192} value={note} onChange={(event) => setNote(event.target.value)} /></label><button type="button" disabled={busy || !note.trim()} onClick={() => void command("note")}>Save note</button>
        <label className="field"><span>Requested job cap (seconds within existing allocation)</span><input type="number" min="1" max="86400" value={seconds} onChange={(event) => setSeconds(event.target.value)} /></label>
        {current.mode === "develop" ? <><label className="field"><span>Generalization statement in Lean</span><textarea maxLength={16384} value={statement} onChange={(event) => setStatement(event.target.value)} /></label><button type="button" disabled={busy || !statement.trim() || !current.research_allocation_id} onClick={() => void command("generalization")}>Request generalization</button></> : null}
        <p className="meta">Notes and pins guide research. Jobs use existing permissions and remaining allocations; completing a request does not establish a proof.</p>
      </div> : null}
      {requests.length ? <details><summary>Memory requests</summary><ul>{requests.map((request, index) => <li key={index}>{String(request.payload.kind || "Request")} · {request.status}{request.detail ? ` · ${request.detail}` : ""}</li>)}</ul></details> : null}
    </>}
    {message ? <p role="status">{message}</p> : null}
  </section>;
}
