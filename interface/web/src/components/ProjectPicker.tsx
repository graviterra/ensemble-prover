import { useEffect, useId, useRef, useState } from "react";
import { catalogError, fetchDirectory } from "../catalog";
import type { CatalogProject, Directory } from "../catalog";

export function ProjectPicker({ value, projects, roots, onChange, error }: {
  value: string; projects: CatalogProject[]; roots: CatalogProject[]; onChange: (path: string) => void; error?: string;
}) {
  const id = useId();
  const [open, setOpen] = useState(false);
  const [path, setPath] = useState("");
  const [directory, setDirectory] = useState<Directory | null>(null);
  const [loading, setLoading] = useState(false);
  const [message, setMessage] = useState("");
  const [revision, setRevision] = useState(0);
  const region = useRef<HTMLDivElement>(null);
  const browseButton = useRef<HTMLButtonElement>(null);
  useEffect(() => { if (open) region.current?.focus(); }, [open]);
  useEffect(() => {
    if (!open || !path) return;
    const controller = new AbortController();
    setLoading(true); setDirectory(null); setMessage("");
    void fetchDirectory(path, controller.signal).then((result) => {
      if (!controller.signal.aborted) setDirectory(result);
    }).catch((cause: unknown) => {
      if (!controller.signal.aborted) setMessage(catalogError(cause));
    }).finally(() => {
      if (!controller.signal.aborted) setLoading(false);
    });
    return () => controller.abort();
  }, [open, path, revision]);
  function close() { setOpen(false); browseButton.current?.focus(); }
  function choose(project: string) { onChange(project); close(); }
  return <div className="project-picker">
    <div className="picker-toolbar">
      <label className="field" htmlFor={`${id}-project`}>
        <span>Project</span>
        <select id={`${id}-project`} value={value} onChange={(event) => onChange(event.target.value)} aria-invalid={Boolean(error)}>
          <option value="">Choose a Lake project</option>
          {value && !projects.some((item) => item.path === value) ? <option value={value}>{value.split("/").filter(Boolean).at(-1) || value} (selected)</option> : null}
          {projects.map((item) => <option value={item.path} key={item.path}>{item.name}</option>)}
        </select>
      </label>
      <button type="button" className="button" ref={browseButton} aria-expanded={open} aria-controls={`${id}-browser`} onClick={() => {
        setPath(value || roots[0]?.path || ""); setOpen(!open);
      }}>Browse folders</button>
    </div>
    {value ? <p className="meta project-path" title={value}>{value}</p> : <p className="meta">Choose a detected project or browse folders on this machine.</p>}
    {error ? <p className="field-error" role="alert">{error}</p> : null}
    {open ? <div className="picker-dialog panel" id={`${id}-browser`} ref={region} role="region" aria-label="Browse project folders" tabIndex={-1} onKeyDown={(event) => {
      if (event.key === "Escape") { event.preventDefault(); close(); }
    }}>
      <div className="picker-toolbar"><h3>Choose a project folder</h3><button className="text-button" type="button" onClick={close}>Close browser</button></div>
      <div className="picker-roots">{roots.map((root) => <button className="button" type="button" key={root.path} onClick={() => setPath(root.path)}>{root.name}</button>)}</div>
      {path ? <p className="meta project-path">{path}</p> : <p>No folders are shared by the service.</p>}
      {loading ? <p role="status">Loading folders…</p> : null}
      {message ? <div role="alert"><p>{message}</p><button className="button" type="button" onClick={() => setRevision((item) => item + 1)}>Retry folders</button></div> : null}
      {directory ? <>
        <div className="picker-toolbar">
          {directory.parent ? <button type="button" className="button" onClick={() => setPath(directory.parent!)}>Up one folder</button> : null}
          {directory.isProject ? <button type="button" className="button button-primary" onClick={() => choose(directory.path)}>Use this project</button> : null}
        </div>
        <ul className="folder-list">{directory.directories.map((item) => <li key={item.path}>
          <button type="button" className="folder-button" onClick={() => setPath(item.path)}><span aria-hidden="true">▸</span> {item.name}</button>
          {item.isProject ? <button type="button" className="text-button" onClick={() => choose(item.path)}>Use {item.name}</button> : null}
        </li>)}</ul>
        {directory.truncated ? <p className="meta">Only part of this large folder was scanned. You can enter a known project path using manual selection below.</p> : !directory.directories.length ? <p className="meta">No more folders here.</p> : null}
      </> : null}
    </div> : null}
    <details className="advanced-fields"><summary>Enter a project path manually</summary><label className="field"><span>Lake project path</span><input value={value} spellCheck={false} onChange={(event) => onChange(event.target.value)} /></label></details>
  </div>;
}
