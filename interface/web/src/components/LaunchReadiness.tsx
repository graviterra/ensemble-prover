import "./launch-readiness.css";

export type LaunchIssue = {
  key: string;
  message: string;
  actionLabel?: string;
  onAction?: () => void;
};

export function LaunchReadiness({ issues, busy }: { issues: LaunchIssue[]; busy: boolean }) {
  return <section className="panel launch-readiness" aria-labelledby="launch-readiness-heading">
    <h2 id="launch-readiness-heading">Launch readiness</h2>
    <p className="readiness-summary" role="status">{busy ? "Starting this run…" : issues.length ? `${issues.length} ${issues.length === 1 ? "item needs" : "items need"} attention` : "Ready to start"}</p>
    {issues.length ? <ul className="readiness-list">{issues.map((issue) => <li key={issue.key}>
      <span>{issue.message}</span>
      {issue.onAction ? <button type="button" className="text-button" onClick={issue.onAction}>{issue.actionLabel}</button> : null}
    </li>)}</ul> : <p className="meta">Required choices are complete. Credentials and the project toolchain have not been checked.</p>}
  </section>;
}
