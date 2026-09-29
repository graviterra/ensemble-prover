import { useState } from "react";
import type { GraphNode } from "../types";
import { formatElapsed, humanize, nodeRole } from "../words";

export function ProofGraph({ nodes, selectedId, onSelect, expanded }: {
  nodes: GraphNode[]; selectedId: string | null; onSelect: (id: string) => void; expanded: boolean;
}) {
  const [limit, setLimit] = useState(expanded ? 25 : 13);
  const [query, setQuery] = useState("");
  const filtered = nodes.filter((node, index) => index === 0 || node.label.toLowerCase().includes(query.trim().toLowerCase()));
  const visible = filtered.slice(0, limit);
  const width = 740;
  const height = Math.max(280, 140 + Math.ceil((visible.length - 1) / 3) * 124);
  const positioned = visible.map((node, index) => ({
    node, x: index === 0 ? 260 : 20 + ((index - 1) % 3) * 240,
    y: index === 0 ? 24 : 148 + Math.floor((index - 1) / 3) * 124,
  }));
  return <>
    {expanded || nodes.length > 13 ? <label className="graph-search">Find a helper<input type="search" value={query} onChange={(event) => setQuery(event.target.value)} placeholder="Search recorded nodes" /></label> : null}
    <div className="graph-frame">
      <div className="graph-scroll" tabIndex={0} aria-label="Proof graph, scroll to explore">
        <div className="proof-canvas" style={{ width, height }}>
          <svg width={width} height={height} className="graph-edges" aria-hidden="true">
            {positioned.flatMap(({ node, x, y }) => (node.supports ?? []).flatMap((support) => {
              const target = positioned.find((item) => item.node.id === support);
              if (!target) return [];
              const middle = (y + 78 + target.y) / 2;
              return [<path key={node.id + ":" + support} d={`M ${x + 110} ${y + 78} V ${middle} H ${target.x + 110} V ${target.y}`} />];
            }))}
          </svg>
          {positioned.map(({ node, x, y }, index) => {
            const role = node.kind ?? nodeRole(index);
            return <button type="button" key={node.id} className={`proof-node ${role === "root" ? "root-node" : "helper-node"}${node.status === "verified_export" ? " verified-node" : ""}`}
              style={{ left: x, top: y }} aria-label={`Select ${role} ${node.label}`} aria-pressed={node.id === selectedId} onClick={() => onSelect(node.id)}>
              <span className="node-kind">{role === "root" ? "Root theorem" : "Recorded helper"} · {humanize(node.status)}</span>
              <span className="node-name" title={node.label}>{node.label}</span>
              <small>{node.recordedAtS != null ? formatElapsed(node.recordedAtS) : role === "root" ? "Export status is shown separately" : "No receipt time reported"}</small>
            </button>;
          })}
          {!nodes.length ? <p className="graph-empty">The run has not returned graph evidence yet.</p> : visible.length === 1 ? <p className="graph-empty">{nodes.length === 1 ? "No helper nodes have been recorded." : "No helpers match this search."}</p> : null}
        </div>
      </div>
      <div className="graph-legend"><span>□ root theorem</span><span>□ recorded helper</span><span>— recorded support</span><span className="selected-legend">→ selected evidence</span></div>
      <details className="graph-text"><summary>Text view of recorded nodes · {nodes.length}</summary><ul>{filtered.map((node) => <li key={node.id}>
        <button type="button" className="text-button mono" onClick={() => onSelect(node.id)}>{node.label}</button> · {humanize(node.status)}
        {node.supports?.length ? <span> · supports: {node.supports.map((id) => nodes.find((item) => item.id === id)?.label || id).join(", ")}</span> : null}
      </li>)}</ul></details>
    </div>
    <div className="graph-count"><span className="meta">Shown: {visible.length} of {nodes.length} recorded nodes.</span>
      {filtered.length > limit ? <button type="button" className="text-button" onClick={() => setLimit((value) => value + 12)}>Show 12 more nodes</button> : null}
    </div>
  </>;
}
