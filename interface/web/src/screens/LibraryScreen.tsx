import { useEffect, useRef, useState } from "react";
import { failureText, fetchLibrary } from "../api";
import { startPolling } from "../polling";
import { sweepAttempt } from "../sweeps";
import { PollingControls } from "../components/PollingControls";
import { defaultResultsFilters, filterResults, normalizeResultsFilters, resultOutcome, resultOutcomes, resultsToQuery, resultTitle } from "../results";
import type { ResultsFilters } from "../results";
import type { LibraryRun } from "../types";
import { classify, formatWhen, humanize } from "../words";
import "../results.css";

export function LibraryScreen({ onOpen, onNew, filters, onFiltersChange }: {
  onOpen: (id: string) => void; onNew: () => void; filters?: ResultsFilters; onFiltersChange?: (filters: ResultsFilters) => void;
}) {
  const [runs, setRuns] = useState<LibraryRun[] | null>(null);
  const [error, setError] = useState("");
  const [loading, setLoading] = useState(true);
  const [localFilters, setLocalFilters] = useState(defaultResultsFilters);
  const [lastUpdated, setLastUpdated] = useState<number | null>(null);
  const [refreshing, setRefreshing] = useState(false);
  const current = filters ?? localFilters;
  const loadRef = useRef<() => Promise<void>>(async () => {});
  function change(patch: Partial<ResultsFilters>) {
    const next = normalizeResultsFilters({ ...current, ...patch });
    if (onFiltersChange) onFiltersChange(next);
    else setLocalFilters(next);
  }

  useEffect(() => {
    let cancelled = false;
    let initial = true;
    const polling = startPolling(async (signal) => {
      const first = initial;
      initial = false;
      setRefreshing(true);
      try {
        const next = await fetchLibrary(signal);
        if (cancelled) return;
        setRuns(next);
        setError("");
        setLastUpdated(Date.now());
      } catch (err) {
        if (cancelled) return;
        setError(failureText(err, "The local service did not answer."));
      } finally {
        if (!cancelled) {
          setRefreshing(false);
          if (first) setLoading(false);
        }
      }
    }, 4000);
    loadRef.current = polling.refresh;
    return () => {
      cancelled = true;
      polling.stop();
    };
  }, []);

  const ordered = filterResults(runs ?? [], current);
  const sweeps = [...new Set((runs ?? []).map((run) => sweepAttempt(run.id)?.sweep).filter((sweep): sweep is string => Boolean(sweep)))].sort().reverse();
  const hasFilters = Boolean(resultsToQuery(current));

  return (
    <section className="results-page">
      <header className="composer-head"><div><h1 className="page-title">Results</h1><p className="lede">Recorded attempts, root outcomes, and export evidence.</p></div><button type="button" className="button button-primary" onClick={onNew}>New run</button></header>
      <PollingControls lastUpdated={lastUpdated} refreshing={refreshing} error={error} onRefresh={() => void loadRef.current()} />
      <dl className="result-stats">
        <div><dt>Matching attempts</dt><dd>{runs ? ordered.length : "—"}</dd></div>
        <div><dt>Verified exports</dt><dd>{runs ? ordered.filter((run) => resultOutcome(run) === "verified").length : "—"}</dd></div>
        <div><dt>Internal solve / export pending</dt><dd>{runs ? ordered.filter((run) => resultOutcome(run) === "internal").length : "—"}</dd></div>
        <div><dt>Reported running</dt><dd>{runs ? ordered.filter((run) => run.launchStatus === "running").length : "—"}</dd></div>
        <div><dt>Export failed</dt><dd>{runs ? ordered.filter((run) => resultOutcome(run) === "export_failed").length : "—"}</dd></div>
      </dl>
      <div className="library-tools">
        <input type="search" aria-label="Search attempts" placeholder="Search theorem, statement, or run" value={current.query} onChange={(event) => change({ query: event.target.value })} />
        <div className="row-actions">
          <button type="button" aria-pressed={current.running} className={current.running ? "button button-primary" : "button"} onClick={() => change({ running: !current.running })}>Running</button>
          <button type="button" className="button" disabled={!hasFilters} onClick={() => change(defaultResultsFilters())}>Clear filters</button>
        </div>
      </div>
      <div className="results-filters">
        <label className="field"><span>Root outcome</span><select value={current.outcome} onChange={(event) => change({ outcome: event.target.value as ResultsFilters["outcome"] })}>
          {resultOutcomes.map(([value, label]) => <option key={value} value={value}>{label}</option>)}
        </select></label>
        <label className="field"><span>Sweep</span><select value={current.sweep} onChange={(event) => change({ sweep: event.target.value })}>
          <option value="">All sweeps and standalone attempts</option>
          {current.sweep && !sweeps.includes(current.sweep) ? <option value={current.sweep}>{current.sweep} (not in loaded attempts)</option> : null}
          {sweeps.map((sweep) => <option key={sweep} value={sweep}>{sweep}</option>)}
        </select></label>
        <label className="field"><span>Sort attempts</span><select value={current.sort} onChange={(event) => change({ sort: event.target.value as ResultsFilters["sort"] })}>
          <option value="recent">Most recent activity</option><option value="oldest">Oldest activity</option><option value="theorem">Theorem name</option>
        </select></label>
      </div>
      <p className="meta results-scope" role="status">{runs ? `Showing ${ordered.length} of ${runs.length} loaded attempts. ` : ""}The library contains up to 500 recent attempts. Counts describe matching loaded attempts, including separate retries and preparation stages.</p>
      {loading ? <p>Reading the results…</p> : null}
      {error ? <div className="notice" role="alert"><p>{error}</p></div> : null}
      {!loading && !error && ordered.length === 0 ? <div className="empty"><p>{(runs ?? []).length === 0 ? "No attempts are in the run folder yet." : "No attempts match these filters."}</p>{(runs ?? []).length === 0 ? <button type="button" className="button" onClick={onNew}>Open launcher</button> : null}</div> : null}
      {ordered.length ? <div className="results-table-wrap" tabIndex={0} aria-label="Run results, scroll for all columns"><table className="results-table">
        <thead><tr><th scope="col">Theorem / run</th><th scope="col">Root outcome</th><th scope="col">Process</th><th scope="col">Export</th><th scope="col">Last recorded</th></tr></thead>
        <tbody>{ordered.map((run) => {
          const view = classify(run);
          return <tr key={run.id}>
            <th scope="row"><button type="button" className="result-link" onClick={() => onOpen(run.id)}>{resultTitle(run)}</button><span className="meta mono result-id">{run.id}</span>
              {run.formalizationStatus ? <span className="meta">Translation: {humanize(run.formalizationStatus)}</span> : null}</th>
            <td><span className={`mark mark-${view.tone}`}>{view.mark}</span>{run.internalSolved ? <p className="meta">Internal solve recorded</p> : null}</td>
            <td>{humanize(run.launchStatus) || "Not reported"}</td>
            <td>{humanize(run.exportState) || "Not reported"}</td>
            <td className="meta">{formatWhen(run.lastWriteTs)}</td>
          </tr>;
        })}</tbody>
      </table></div> : null}
      <p className="meta results-footnote">Internal solves, process exit, and verified exports are separate outcomes. Open a run to inspect its graph and receipts.</p>
    </section>
  );
}
