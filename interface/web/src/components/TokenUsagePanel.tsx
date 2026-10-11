import type { TokenUsage } from "../tokenUsage";
import { formatElapsed, humanize } from "../words";
import "./token-usage.css";

const number = (value: number | null | undefined) => value == null ? "Not reported" : value.toLocaleString();
const roleNames = new Map([["prove", "Prover"], ["refine", "Refiner"], ["planner", "Planner"], ["llm", "LLM"]]);
const roleName = (role: string) => roleNames.get(role) || humanize(role);

export function TokenUsagePanel({ value, paused, readFailed, lastEventS, traceAgeS }: {
  value?: TokenUsage; paused: boolean; readFailed: boolean; lastEventS?: number | null; traceAgeS?: number | null;
}) {
  const sums = value?.totals;
  return <section className="token-usage" aria-label="Token usage">
    <div className="token-heading"><h2>Token usage</h2><span className="meta">{readFailed ? "Last successful read" : paused ? "Updates paused" : "Updates every 4 seconds"}</span></div>
    <dl className="token-totals">
      <div><dt>Input tokens</dt><dd>{number(sums?.input_tokens)}</dd><small>Includes cached input</small></div>
      <div><dt>Generated tokens</dt><dd>{number(sums?.output_tokens)}</dd><small>Includes reported reasoning</small></div>
      <div><dt>Cached input</dt><dd>{number(sums?.cached_input_tokens)}</dd><small>Reported cache reads</small></div>
    </dl>
    <p className="meta">Reported usage in the loaded trace, across all roles. Calls still running are added when usage arrives.
      {value?.lastUsageS != null ? ` Last usage receipt: ${formatElapsed(value.lastUsageS)} into the run.` : value?.reportedReceipts ? " Receipt time not recorded." : " No token receipt has arrived yet."}</p>
    {value?.incompleteBreakdowns ? <p className="meta">Cache or reasoning breakdowns were missing from {value.incompleteBreakdowns} reports; these subsets may be incomplete.</p> : null}
    {value?.backlog ? <p className="notice">Reading earlier events; these totals are still catching up.</p> : null}
    {value?.partial ? <p className="notice">The retained trace or display is incomplete. These totals may exclude earlier work or reports without a stable identity.</p> : null}
    {value?.incompleteReceipts ? <p className="notice">{value.incompleteReceipts} usage reports were incomplete. Late receipts are included as they arrive; unreported consumption is not counted as zero.</p> : null}
    {value?.calls.length ? <div className="token-calls"><h3>Calls awaiting usage</h3><ul>{value.calls.map(call => {
      const age = call.elapsedS != null && lastEventS != null && traceAgeS != null ? Math.max(0, lastEventS - call.elapsedS) + traceAgeS : null;
      return <li key={call.requestId}>
        <div><strong>{roleName(call.role) || "LLM"}</strong>{call.model ? ` · ${call.model}` : ""}<small>{call.scope || "Scope not recorded"} · {humanize(call.status) || "Status not recorded"}{age != null && age > 120 ? " · stale observation" : ""}</small></div>
        <div>{call.thinkingBlockTokens != null ? <><strong>≈ {number(call.thinkingBlockTokens)}</strong><small>Last observed thinking block · estimate</small></> : <small>Waiting for provider token usage</small>}</div>
      </li>;
    })}</ul><p className="meta">Thinking estimates can reset between blocks. They are not whole-request totals and are never added to reported usage. Some providers report tokens only after a call completes.</p></div> : null}
    {value?.roles.length ? <details><summary>Usage by role · {value.reportedReceipts} reported {value.reportedReceipts === 1 ? "receipt" : "receipts"}</summary><div className="token-table"><table><thead><tr><th>Role</th><th>Input</th><th>Generated</th><th>Reasoning</th><th>Cache reads</th><th>Cache writes</th></tr></thead><tbody>{value.roles.map(row => <tr key={row.role}><th>{roleName(row.role)}</th><td>{number(row.input_tokens)}</td><td>{number(row.output_tokens)}</td><td>{number(row.reasoning_output_tokens)}</td><td>{number(row.cached_input_tokens)}</td><td>{number(row.cache_write_tokens)}</td></tr>)}</tbody></table></div><p className="meta">Reasoning is part of generated tokens; cache reads and writes are part of input. Provider breakdowns may be incomplete.</p></details> : null}
  </section>;
}
