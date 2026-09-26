import "./polling-controls.css";

export function PollingControls({ lastUpdated, refreshing, error = "", paused = false, onPauseChange, onRefresh }: {
  lastUpdated: number | null;
  refreshing: boolean;
  error?: string;
  paused?: boolean;
  onPauseChange?: (paused: boolean) => void;
  onRefresh: () => void;
}) {
  const state = error
    ? lastUpdated === null ? "Read failed; no data received yet." : "Read failed; showing the last successful read."
    : refreshing ? "Reading recorded data…" : paused ? "Automatic updates paused." : "Automatic updates every 4 seconds.";
  return <div className={`polling-controls${error ? " has-read-error" : ""}`} aria-label="Recorded data updates">
    <div>
      <p className="meta">{state}</p>
      {lastUpdated !== null ? <p className="meta">Last successful read: <time dateTime={new Date(lastUpdated).toISOString()}>{new Date(lastUpdated).toLocaleTimeString()}</time></p> : null}
      {paused ? <p className="meta">The prover keeps working while this view is paused.</p> : null}
    </div>
    <div className="row-actions">
      <button type="button" className="button" disabled={refreshing} onClick={onRefresh}>{refreshing ? "Reading…" : error ? "Retry now" : "Refresh now"}</button>
      {onPauseChange ? <button type="button" className="button" aria-pressed={paused} onClick={() => onPauseChange(!paused)}>{paused ? "Resume updates" : "Pause updates"}</button> : null}
    </div>
  </div>;
}
