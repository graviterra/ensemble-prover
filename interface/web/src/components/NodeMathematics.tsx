import type { NodeEvidence } from "../types";
import "./node-mathematics.css";

export function NodeMathematics({ evidence }: { evidence?: NodeEvidence }) {
  const available = Boolean(evidence?.statement || evidence?.leanSource);
  return <section className="node-mathematics" aria-label="Selected formal mathematics">
    <h3>Formal mathematics</h3>
    {available ? <>
      <p className="meta">{evidence?.source || "Recorded mathematical source"}{evidence?.scope ? ` · scope: ${evidence.scope}` : ""}</p>
      {evidence?.statement ? <><h4>Lean statement</h4><pre className="mathematics-source">{evidence.statement}</pre></> : null}
      {evidence?.leanSource ? <details><summary>Recorded Lean proof source</summary><pre className="mathematics-source">{evidence.leanSource}</pre></details> : null}
      {evidence?.reason ? <p className="meta">{evidence.reason}</p> : null}
      <p className="meta">Recorded source is shown for inspection. Root status and export verification are reported separately.</p>
    </> : <p className="meta">{evidence?.reason || "No formal statement or proof source is available for this node in the retained records."}</p>}
  </section>;
}
