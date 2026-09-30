import { useId } from "react";
import type { LiveMathView, RuntimeSetting } from "../liveMath";
import { formatElapsed, humanize } from "../words";
import "./liveMath.css";

const missing = "Not recorded";
function at(value: number | null | undefined) { return value != null ? `At ${formatElapsed(value)} elapsed` : "Time not recorded"; }
function knownScope(value: string | undefined) {
  const label = value?.trim() || "";
  return ["not recorded", "unscoped", "unknown"].includes(label.toLowerCase()) ? "" : label;
}
function isChildScope(value: string | undefined) { return knownScope(value) === "subgoal" || /^child:.+/.test(knownScope(value)); }
function scope(value: string | undefined) {
  const label = knownScope(value);
  return label === "problem" ? "Original theorem" : isChildScope(label) ? `Child scope · ${label}` : label ? `Scope · ${label}` : "Scope not recorded";
}
function sourceName(value: string) {
  return value === "prepared" ? "Prepared request · dispatch not confirmed" : value === "request" ? "Recorded request" : value === "startup" ? "Startup configuration" : value === "ambiguous" ? "Unresolved provider selection" : "Evidence source not recorded";
}
function Setting({ item }: { item: RuntimeSetting }) {
  return <div className="runtime-setting-row">
    <div className="runtime-model-cell"><span className="eyebrow">{humanize(item.role) || "Role not recorded"}</span><strong className="runtime-model">{item.model || "Model not recorded"}</strong></div>
    <div><span className="meta">Effective reasoning</span><strong>{item.reasoning || missing}</strong></div>
    <div><span className="meta">Output allowance</span><strong>{item.outputTokens != null ? `${item.outputTokens.toLocaleString("en-US")} tokens` : missing}</strong></div>
    <div className="runtime-receipt-cell"><span>{sourceName(item.source)}</span><span className="meta">{at(item.elapsedS)}{item.scope ? ` · ${scope(item.scope)}` : ""}</span></div>
  </div>;
}
function SettingDetails({ item }: { item: RuntimeSetting }) {
  return <article className="runtime-setting-details"><h3>{humanize(item.role) || "Role not recorded"}</h3><dl>
    {item.requestedReasoning ? <div><dt>Requested reasoning</dt><dd>{item.requestedReasoning}</dd></div> : null}
    <div><dt>Transport</dt><dd>{humanize(item.transport) || missing}</dd></div>
    {item.workType ? <div><dt>Work</dt><dd>{humanize(item.workType)}</dd></div> : null}
    <div><dt>Scope</dt><dd>{scope(item.scope)}</dd></div>
    {item.requestId ? <div><dt>Request identity</dt><dd className="mono">{item.requestId}</dd></div> : null}
  </dl></article>;
}

export function LiveMathPanel({ value, paused = false, readFailed = false }: {
  value?: LiveMathView; paused?: boolean; readFailed?: boolean;
}) {
  const heading = useId();
  const selected = value?.selection;
  const activity = value?.activity;
  const scopedActivity = activity && activity.scope !== "problem" && (activity.dispatchId !== selected?.dispatchId || activity.scope !== selected?.scope);
  const receipt = value?.lastCostlyAction;
  const health = value?.health;
  const alerts = Boolean(health?.activeDeferrals.length || health?.providerIssues.length || health?.omittedDeferrals || health?.backlog || health?.partialTrace || health?.traceAvailable === false);
  const source = value?.source;
  return <section className="live-math" aria-labelledby={heading}>
    <header className="math-focus-header">
      <div><p className="eyebrow">Proof search, explained</p><h2 id={heading}>Mathematical focus</h2></div>
      <span className="mark mark-plain">Recorded decisions · heuristic priorities</span>
    </header>
    {paused || readFailed || health?.stale || health?.backlog || health?.partialTrace || health?.traceAvailable === false ? <div className="math-observation-notice">
      {paused ? <p>Updates paused. This view retains the evidence already read.</p> : null}
      {readFailed ? <p>Connection unavailable; mathematical focus shows the last successful read.</p> : null}
      {health?.traceAvailable === false ? <p>Trace unavailable. This view retains previously read evidence until the trace can be read again.</p> : null}
      {health?.stale ? <p>No recent trace writes. An expensive action may still be running; silence alone does not establish a stall.</p> : null}
      {health?.backlog ? <p>Reading accumulated events. The displayed decision may lag current work.</p> : null}
      {health?.partialTrace ? <p>Trace coverage is partial. Earlier decisions or outcomes may be unavailable.</p> : null}
    </div> : null}
    <div className="math-focus-grid">
      <article className="math-blocker">
        <p className="eyebrow">{selected?.status === "completed" ? "Last recorded approach" : "Active approach"}</p>
        <h3>{selected?.approach || missing}</h3>
        <p className="meta">{scope(selected?.scope)}{selected?.elapsedS != null ? ` · ${at(selected.elapsedS)}` : ""}</p>
        <h4>{selected?.connection === "declared_requirement" ? "Blocking route obligation" : "Selected obligation"}</h4>
        {selected?.statement ? <pre className="math-obligation" tabIndex={0} aria-label="Blocking obligation in Lean">{selected.statement}</pre> : <p className="meta">Not recorded. This run has no retained formal target for the selected action.</p>}
        {selected?.statementTruncated ? <p className="meta">Statement preview truncated. Consult the run’s saved formal target for the complete obligation.</p> : null}
        {selected?.status === "completed" ? <p className="meta">This action completed. Its selected obligation is historical until another dispatch is recorded.</p> : <p className="meta">The selected obligation describes where work was directed. Its priority is not a mathematical certificate.</p>}
        {selected && (selected.obligationId || selected.approachId || selected.connection || selected.openRequirements != null) ? <details className="math-route-details">
          <summary>Inspect root connection</summary>
          <dl>
            {selected.approachId ? <div><dt>Approach</dt><dd className="mono">{selected.approachId}</dd></div> : null}
            {selected.obligationId ? <div><dt>Obligation</dt><dd className="mono">{selected.obligationId}</dd></div> : null}
            <div><dt>Recorded connection</dt><dd>{selected.connection === "declared_requirement" ? "Declared route prerequisite; not a checked reduction" : selected.connection === "unclassified" ? "Root contribution not yet classified" : selected.connection || missing}</dd></div>
            {selected.openRequirements != null ? <div><dt>Open route requirements</dt><dd>{selected.openRequirements}</dd></div> : null}
          </dl>
        </details> : null}
      </article>
      <div className="math-decision-column">
        <article className="math-decision">
          <p className="eyebrow">Why this action</p>
          <div className="math-action-title"><h3>{humanize(selected?.action || "") || missing}</h3>
            {selected?.status !== "unknown" && selected?.status ? <span className="mark">{selected.status === "completed" ? "Completed" : "Dispatched"}</span> : null}</div>
          <p>{selected?.reason || "The dispatch explanation was not recorded. A future scheduler decision is not yet known."}</p>
          {scopedActivity ? <div className="math-child-activity"><strong>{isChildScope(activity.scope) ? "Latest child activity" : "Latest activity · scope not classified"}</strong><p>{humanize(activity.action) || missing} · {activity.status === "completed" ? "completed" : activity.status === "selected" ? "dispatched" : "status unknown"}</p><p className="meta">{scope(activity.scope)} · {at(activity.elapsedS)}</p>{activity.statement ? <details><summary>Inspect activity target</summary><pre className="math-obligation">{activity.statement}</pre>{activity.statementTruncated ? <p className="meta">Statement preview truncated. Consult the saved formal target for the complete obligation.</p> : null}</details> : null}</div> : null}
        </article>
        <article className="math-last-action">
          <p className="eyebrow">Last expensive action · ≥20 seconds</p>
          <h3>{receipt ? humanize(receipt.action) || "Recorded action" : missing}</h3>
          {receipt ? <><p>{receipt.result || "The outcome was not recorded."}</p><p className="meta">{scope(receipt.scope)} · {receipt.durationS != null ? `${formatElapsed(receipt.durationS)} spent` : "Duration not recorded"} · {at(receipt.elapsedS)}</p>{receipt.leanStatus ? <p className="meta">Lean receipt: {humanize(receipt.leanStatus)}</p> : null}</> : <p className="meta">No completed action meeting this duration threshold has been recorded.</p>}
        </article>
      </div>
    </div>
    <div className="math-runtime">
      <div className="math-runtime-summary">
        <div><p className="eyebrow">Running source</p><strong className="mono">{source?.commit ? source.commit.slice(0, 12) : missing}</strong><p className="meta">{source?.dirty === true ? "Modified checkout" : source?.dirty === false ? "Clean checkout at startup" : "Checkout state not recorded"}</p></div>
        <div><p className="eyebrow">Infrastructure observations</p><strong>{health?.processStatus ? humanize(health.processStatus) : "Process state not recorded"}</strong><p className="meta">{health?.traceAgeS != null ? `Trace last written ${formatElapsed(health.traceAgeS)} ago` : "Trace age not recorded"}</p></div>
        <span className={`mark ${alerts ? "mark-unresolved" : "mark-plain"}`}>{alerts ? "Attention reported" : health ? "No active deferrals reported" : "Health not recorded"}</span>
      </div>
      {health?.activeDeferrals.length || health?.providerIssues.length || health?.omittedDeferrals ? <ul className="math-health-events">
        {health.activeDeferrals.map((item, index) => <li key={`defer-${index}`}><strong>{humanize(item.action) || "Action"} deferred</strong> · {item.reason || "Reason not recorded"}<span className="meta"> · {scope(item.scope)}</span></li>)}
        {health.providerIssues.map((item, index) => <li key={`provider-${index}`}><strong>{humanize(item.role) || "Provider"}</strong> · {humanize(item.status) || "Issue recorded"}<span className="meta"> · {scope(item.scope)} · {at(item.elapsedS)}</span></li>)}
        {health.omittedDeferrals > 0 ? <li className="meta">{health.omittedDeferrals} deferral observations are not displayed. Active status may be incomplete.</li> : null}
      </ul> : null}
      <div className="runtime-settings" aria-label="Recorded model settings">
        {value?.settings.length ? value.settings.map((item, index) => <Setting item={item} key={`${item.role}-${index}`} />) : <p className="meta runtime-empty">Not recorded. Older runs may not include effective request settings.</p>}
      </div>
      <details className="math-runtime-details">
        <summary>Inspect runtime evidence <span className="meta">· reasoning, transport & source identity</span></summary>
        {value?.settings.length ? <div className="runtime-details-grid">{value.settings.map((item, index) => <SettingDetails item={item} key={`${item.role}-${index}`} />)}</div> : null}
        <p className="meta runtime-footnote">Settings describe the recorded startup or request, and may change on later calls. Prepared requests do not confirm provider dispatch. Requested reasoning is separate from effective reasoning. Infrastructure observations do not certify mathematical progress.</p>
        {source?.commit || source?.fingerprint ? <details className="math-source-details"><summary>Inspect source identity</summary><dl>
          {source.commit ? <div><dt>Startup commit</dt><dd className="mono">{source.commit}</dd></div> : null}
          {source.fingerprint ? <div><dt>Source fingerprint</dt><dd className="mono">{source.fingerprint}</dd></div> : null}
          {source.partial ? <div><dt>Coverage</dt><dd>Source fingerprint coverage is partial.</dd></div> : null}
        </dl></details> : null}
      </details>
    </div>
  </section>;
}
