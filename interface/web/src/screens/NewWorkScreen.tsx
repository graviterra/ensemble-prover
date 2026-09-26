import { useEffect, useRef, useState } from "react";
import type { FormEvent } from "react";
import { failureText, postAttempt, readId } from "../api";
import { catalogError, fetchOptions, fetchProject, fetchTheorems, usesCliModel } from "../catalog";
import type { OptionField, ProjectFiles, Theorems } from "../catalog";
import { LaunchReadiness } from "../components/LaunchReadiness";
import type { LaunchIssue } from "../components/LaunchReadiness";
import { ModelPicker } from "../components/ModelPicker";
import { ProjectPicker } from "../components/ProjectPicker";
import { LaunchOptions, loadProfile, optionPayload, saveProfile } from "../components/LaunchOptions";
import { useCatalog } from "../components/useCatalog";
import { completeStartSubmission, loadDrafts, loadSetup, prepareStartSubmission, saveDrafts, saveSetup, StartIdentityStorageError } from "../storage";
import type { Drafts } from "../storage";

function persist(next: Drafts) {
  try { saveDrafts(next); } catch { /* The current page retains the draft. */ }
}

export function NewWorkScreen({ onOpen, onLibrary }: { onOpen: (id: string) => void; onLibrary: () => void }) {
  const [drafts, setDrafts] = useState<Drafts>(() => loadDrafts(loadSetup()));
  const mode = drafts.start === "lean" ? "lean" : "english";
  const { catalog, error: catalogMessage, loading: catalogLoading, retry } = useCatalog();
  const [files, setFiles] = useState<ProjectFiles | null>(null);
  const [theorems, setTheorems] = useState<Theorems | null>(null);
  const [fileLoading, setFileLoading] = useState(false);
  const [theoremLoading, setTheoremLoading] = useState(false);
  const [sourceError, setSourceError] = useState("");
  const [sourceRevision, setSourceRevision] = useState(0);
  const [filter, setFilter] = useState("");
  const [profile, setProfile] = useState(loadProfile);
  const [fields, setFields] = useState<OptionField[]>([]);
  const [optionError, setOptionError] = useState("");
  const [optionRevision, setOptionRevision] = useState(0);
  const [errors, setErrors] = useState<Record<string, string>>({});
  const [notice, setNotice] = useState("");
  const [busy, setBusy] = useState(false);
  const mounted = useRef(false);
  const submitting = useRef(false);
  useEffect(() => {
    mounted.current = true;
    return () => { mounted.current = false; };
  }, []);
  const current = mode === "lean" ? drafts.lean : drafts.english;
  const translateOnly = mode === "english" && drafts.english.formalizeOnly;

  function update(change: (previous: Drafts) => Drafts) {
    setDrafts((previous) => { const next = change(previous); persist(next); return next; });
  }
  function patchCurrent(patch: { projectPath?: string; prover?: string; proverModel?: string }) {
    update((previous) => mode === "lean" ? { ...previous, lean: { ...previous.lean, ...patch } } : { ...previous, english: { ...previous.english, ...patch } });
  }
  function chooseProject(projectPath: string) {
    setFiles(null); setTheorems(null); setFilter("");
    update((previous) => mode === "lean"
      ? { ...previous, lean: { ...previous.lean, projectPath, leanFile: "", theorem: "" } }
      : { ...previous, english: { ...previous.english, projectPath } });
  }
  function changeProfile(next: typeof profile) { setProfile(next); saveProfile(next); }

  useEffect(() => {
    if (!catalog || catalog.projects.length !== 1) return;
    const projectPath = catalog.projects[0].path;
    update((previous) => ({
      ...previous,
      lean: { ...previous.lean, projectPath: previous.lean.projectPath || projectPath },
      english: { ...previous.english, projectPath: previous.english.projectPath || projectPath },
    }));
  }, [catalog]);

  useEffect(() => {
    const controller = new AbortController();
    setOptionError("");
    void fetchOptions(controller.signal).then((result) => {
      if (!controller.signal.aborted) setFields(result);
    }).catch((error: unknown) => {
      if (!controller.signal.aborted) setOptionError(catalogError(error));
    });
    return () => controller.abort();
  }, [optionRevision]);

  useEffect(() => {
    setFiles(null); setTheorems(null); setSourceError("");
    if (mode !== "lean" || !drafts.lean.projectPath) { setFileLoading(false); return; }
    const project = drafts.lean.projectPath;
    const controller = new AbortController();
    setFileLoading(true);
    void fetchProject(project, controller.signal).then((result) => {
      if (controller.signal.aborted) return;
      setFiles(result);
      if (result.files.length === 1) update((previous) => {
        if (previous.lean.projectPath !== project || previous.lean.leanFile) return previous;
        return { ...previous, lean: { ...previous.lean, leanFile: result.files[0].path, theorem: "" } };
      });
    }).catch((error: unknown) => {
      if (!controller.signal.aborted) setSourceError(catalogError(error));
    }).finally(() => { if (!controller.signal.aborted) setFileLoading(false); });
    return () => controller.abort();
  }, [mode, drafts.lean.projectPath, sourceRevision]);

  useEffect(() => {
    setTheorems(null);
    const project = drafts.lean.projectPath, file = drafts.lean.leanFile;
    if (mode !== "lean" || !project || !file) { setTheoremLoading(false); return; }
    const controller = new AbortController();
    setTheoremLoading(true); setSourceError("");
    void fetchTheorems(project, file, controller.signal).then((result) => {
      if (controller.signal.aborted) return;
      setTheorems(result);
      if (result.theorems.length === 1) update((previous) => {
        if (previous.lean.projectPath !== project || previous.lean.leanFile !== file || previous.lean.theorem) return previous;
        return { ...previous, lean: { ...previous.lean, theorem: result.theorems[0].name } };
      });
    }).catch((error: unknown) => {
      if (!controller.signal.aborted) setSourceError(catalogError(error));
    }).finally(() => { if (!controller.signal.aborted) setTheoremLoading(false); });
    return () => controller.abort();
  }, [mode, drafts.lean.projectPath, drafts.lean.leanFile, sourceRevision]);

  async function submit(event: FormEvent) {
    event.preventDefault();
    if (submitting.current) return;
    setErrors(Object.fromEntries(readinessIssues.map((issue) => [issue.key, issue.message])));
    if (readinessIssues.length) return;
    submitting.current = true;
    setBusy(true); setNotice("");
    let idempotencyKey = "";
    try {
      const payload: Record<string, unknown> = mode === "lean"
        ? { kind: "lean", projectPath: current.projectPath.trim(), leanFile: drafts.lean.leanFile.trim(), theorem: drafts.lean.theorem.trim() }
        : { kind: "english", projectPath: current.projectPath.trim(), text: drafts.english.text.trim(), formalizeOnly: drafts.english.formalizeOnly };
      if (!translateOnly) {
        payload.prover = current.prover.trim();
        if (current.proverModel.trim()) payload.proverModel = current.proverModel.trim();
        if (profile.customRefiner) {
          payload.refiner = profile.refiner.trim();
          if (profile.refinerModel.trim()) payload.refinerModel = profile.refinerModel.trim();
        }
        if (Object.keys(launchOptions).length) payload.options = launchOptions;
      }
      const prepared = prepareStartSubmission(mode, payload);
      idempotencyKey = prepared.idempotencyKey;
      const body = await postAttempt(prepared.payload);
      const id = readId(body);
      if (id) {
        completeStartSubmission(mode, idempotencyKey);
        if (mounted.current) onOpen(id);
        return;
      }
      if (mounted.current) setNotice("The service did not return an attempt identity. Work may have started; check the library before retrying.");
    } catch (error) {
      if (idempotencyKey && error && typeof error === "object" && (error as { code?: unknown }).code === "launch_failed") completeStartSubmission(mode, idempotencyKey);
      if (mounted.current) setNotice(error instanceof StartIdentityStorageError ? error.message : failureText(error, "The service could not start this work."));
    } finally {
      submitting.current = false;
      if (mounted.current) setBusy(false);
    }
  }

  const selectedProvider = catalog?.providers.find((provider) => provider.id === current.prover);
  const selectedTheorem = theorems?.theorems.find((theorem) => theorem.name === drafts.lean.theorem);
  const shownFiles = files?.files.filter((file) => file.path === drafts.lean.leanFile || file.path.toLocaleLowerCase().includes(filter.toLocaleLowerCase())) ?? [];
  const explicitOptions = Object.entries(profile.options).filter(([, value]) => value !== "");

  function focusField(id: string) {
    const sourceMissing = id === "lean-file" && (fileLoading || !files?.files.length);
    const declarationsMissing = id === "theorem-choice" && (theoremLoading || !theorems?.theorems.length);
    const target = sourceMissing ? "lean-file-manual" : declarationsMissing ? "theorem-manual" : id;
    const container = document.getElementById(target);
    if (!container) return;
    const field = container.matches("input, select, textarea") ? container : container.querySelector<HTMLElement>("input, select, textarea") ?? container;
    const details = field.closest("details");
    if (details) details.open = true;
    field.focus();
    field.scrollIntoView?.({ block: "center" });
  }

  const readinessIssues: LaunchIssue[] = [];
  function needs(key: string, message: string, actionLabel: string, target: string) {
    readinessIssues.push({ key, message, actionLabel, onAction: () => focusField(target) });
  }
  if (catalogLoading) readinessIssues.push({ key: "service", message: "Checking local service availability…" });
  else if (!catalog || catalogMessage) readinessIssues.push({ key: "service", message: "Connect to the local service to start work.", actionLabel: "Check service again", onAction: retry });
  else if (!catalog.control) readinessIssues.push({ key: "service", message: "Starting work is disabled in read-only mode." });
  if (!current.projectPath.trim()) needs("project", "Choose a Lake project.", "Choose project", "launch-project");
  if (mode === "english" && !drafts.english.text.trim()) needs("text", "Enter the statement to formalize.", "Write statement", "statement");
  if (mode === "lean") {
    if (!drafts.lean.leanFile.trim()) needs("file", "Choose a Lean file.", "Choose Lean file", "lean-file");
    if (!drafts.lean.theorem.trim()) needs("source", "Choose a theorem to prove.", "Choose theorem", "theorem-choice");
  }
  if (!translateOnly) {
    if (!current.prover.trim()) needs("provider", "Choose the provider that will search for a proof.", "Choose prover", "prover-provider");
    else if (!usesCliModel(current.prover.trim()) && !current.proverModel.trim()) needs("provider", "Choose the prover model.", "Choose prover model", "prover-model");
    if (profile.customRefiner) {
      if (!profile.refiner.trim()) needs("refiner", "Choose the separate refiner provider.", "Choose refiner", "refiner-provider");
      else if (!usesCliModel(profile.refiner.trim()) && !profile.refinerModel.trim()) needs("refiner", "Choose the refiner model.", "Choose refiner model", "refiner-model");
    }
  }
  let launchOptions: Record<string, string | number | boolean> = {};
  if (!translateOnly) {
    try { launchOptions = optionPayload(profile.options, fields); }
    catch (error) { readinessIssues.push({ key: "options", message: catalogError(error), actionLabel: "Review launch settings", onAction: () => {
      const settings = document.getElementById("launch-options");
      settings?.focus();
      settings?.scrollIntoView?.({ block: "center" });
    } }); }
  }

  return <section className="composer">
    <header className="composer-head">
      <div><h1 className="page-title">Prepare a run</h1><p className="lede">Choose your theorem and the providers that will work on it.</p></div>
      <div className="segmented" role="group" aria-label="What to start">
        {(["english", "lean"] as const).map((kind) => <button type="button" key={kind} className={mode === kind ? "segment is-selected" : "segment"} aria-pressed={mode === kind} onClick={() => {
          update((previous) => ({ ...previous, start: kind })); setErrors({}); setNotice("");
        }}>{kind === "english" ? "English or LaTeX" : "Lean theorem"}</button>)}
      </div>
    </header>
    {catalogLoading ? <p className="meta" role="status">Discovering projects and providers…</p> : null}
    {catalogMessage ? <div className="notice" role="alert"><p>{catalogMessage}</p><button type="button" className="button" onClick={retry}>Retry discovery</button></div> : null}
    {catalog && !catalog.control ? <p className="notice">This service is in read-only mode. Starting work is turned off.</p> : null}
    <form className="launcher-layout layout" onSubmit={(event) => void submit(event)}>
      <div className="column composer-main">
        <section className="panel">
          <h2>Theorem</h2>
          {mode === "english" ? <label className="field" htmlFor="statement"><span>Statement</span>
            <textarea id="statement" rows={7} placeholder="State the result you want to prove, in English or LaTeX…" value={drafts.english.text} onChange={(event) => update((previous) => ({ ...previous, english: { ...previous.english, text: event.target.value } }))} aria-invalid={Boolean(errors.text)} />
            {errors.text ? <span className="field-error">{errors.text}</span> : null}
          </label> : null}
          <div id="launch-project"><ProjectPicker value={current.projectPath} projects={catalog?.projects ?? []} roots={catalog?.roots ?? []} onChange={chooseProject} error={errors.project} /></div>
          {mode === "lean" ? <>
            <label className="field"><span>Find a Lean file</span><input type="search" value={filter} onChange={(event) => setFilter(event.target.value)} placeholder="Filter files by name…" /></label>
            <label className="field" htmlFor="lean-file"><span>Lean file</span>
              <select id="lean-file" value={drafts.lean.leanFile} disabled={!current.projectPath || fileLoading} onChange={(event) => {
                setTheorems(null); update((previous) => ({ ...previous, lean: { ...previous.lean, leanFile: event.target.value, theorem: "" } }));
              }}>
                <option value="">{fileLoading ? "Loading Lean files…" : "Choose a Lean file"}</option>
                {drafts.lean.leanFile && !files?.files.some((file) => file.path === drafts.lean.leanFile) ? <option value={drafts.lean.leanFile}>{drafts.lean.leanFile} (saved)</option> : null}
                {shownFiles.map((file) => <option key={file.path} value={file.path}>{file.path}</option>)}
              </select>
            </label>
            {files?.truncated ? <p className="meta">This project has more files than the browser can list. Enter a relative file path under advanced selection.</p> : null}
            <label className="field" htmlFor="theorem-choice"><span>Theorem</span>
              <select id="theorem-choice" value={drafts.lean.theorem} disabled={!drafts.lean.leanFile || theoremLoading} onChange={(event) => update((previous) => ({ ...previous, lean: { ...previous.lean, theorem: event.target.value } }))}>
                <option value="">{theoremLoading ? "Reading declarations…" : "Choose a theorem"}</option>
                {drafts.lean.theorem && !theorems?.theorems.some((theorem) => theorem.name === drafts.lean.theorem) ? <option value={drafts.lean.theorem}>{drafts.lean.theorem} (saved)</option> : null}
                {theorems?.theorems.map((theorem) => <option key={theorem.name} value={theorem.name}>{theorem.name}</option>)}
              </select>
            </label>
            {selectedTheorem?.statement ? <pre className="statement-preview">{selectedTheorem.statement}</pre> : null}
            {theorems?.notice ? <p className="meta">{theorems.notice}</p> : null}
            {theorems?.truncated ? <p className="meta">Only the first {theorems.theorems.length} declarations are listed. Advanced theorem selection accepts a full declaration name.</p> : null}
            {theorems && !theorems.theorems.length ? <p className="meta">No selectable theorem was detected. Choose another file or enter its full declaration name below.</p> : null}
            {errors.source ? <p className="field-error" role="alert">{errors.source}</p> : null}
            {sourceError ? <div role="alert"><p>{sourceError}</p><button type="button" className="button" onClick={() => setSourceRevision((value) => value + 1)}>Retry source scan</button></div> : null}
            <details className="advanced-fields"><summary>Advanced theorem selection</summary>
              <label className="field"><span>Relative Lean file</span><input id="lean-file-manual" value={drafts.lean.leanFile} onChange={(event) => update((previous) => ({ ...previous, lean: { ...previous.lean, leanFile: event.target.value, theorem: "" } }))} /></label>
              <label className="field"><span>Full theorem name</span><input id="theorem-manual" value={drafts.lean.theorem} onChange={(event) => update((previous) => ({ ...previous, lean: { ...previous.lean, theorem: event.target.value } }))} /></label>
            </details>
          </> : <label className="check" htmlFor="formalize-only"><input id="formalize-only" type="checkbox" checked={drafts.english.formalizeOnly} onChange={(event) => update((previous) => ({ ...previous, english: { ...previous.english, formalizeOnly: event.target.checked } }))} /><span>Translate only, do not search for a proof yet</span></label>}
        </section>
        <section className="panel"><h2>Provider roles</h2>
          {mode === "english" ? <div className="role"><p className="role-name">Translation · OpenAI</p><p className="meta">{catalog?.providers.find((item) => item.id === "openai")?.availability || "Uses the translation provider configured in the service environment."}</p></div> : null}
          {!translateOnly ? <>
            <div className="role"><h3>Prover</h3><ModelPicker id="prover" providers={catalog?.providers ?? []} provider={current.prover} model={current.proverModel} onChange={(prover, proverModel) => patchCurrent({ prover, proverModel })} error={errors.provider} /></div>
            <div className="role"><label className="check"><input type="checkbox" checked={profile.customRefiner} onChange={(event) => changeProfile({ ...profile, customRefiner: event.target.checked })} /><span>Choose a separate refiner</span></label>
              {profile.customRefiner ? <ModelPicker id="refiner" providers={catalog?.providers ?? []} provider={profile.refiner} model={profile.refinerModel} onChange={(refiner, refinerModel) => changeProfile({ ...profile, refiner, refinerModel })} error={errors.refiner} /> : <p className="meta">Refiner settings are omitted; the CLI resolves its defaults.</p>}
            </div>
            <button type="button" className="text-button" onClick={() => {
              try { saveSetup({ projectPath: current.projectPath, prover: current.prover, proverModel: current.proverModel }); setNotice("Project and prover saved as browser defaults."); }
              catch { setNotice("The browser could not save these defaults."); }
            }}>Save project and prover as defaults</button>
          </> : <p className="meta">Translation produces a Lean statement for inspection. It does not establish a proof.</p>}
        </section>
        {!translateOnly ? <div className="launch-options-group" id="launch-options" tabIndex={-1}>
          {optionError ? <div className="notice" role="alert"><p>{optionError}</p><button type="button" className="button" onClick={() => setOptionRevision((value) => value + 1)}>Retry launch settings</button></div> : null}
          <LaunchOptions fields={fields} values={profile.options} onChange={(options) => changeProfile({ ...profile, options })} />
        </div> : null}
      </div>
      <aside className="column composer-settings">
        <LaunchReadiness issues={readinessIssues} busy={busy} />
        <section className="panel"><h2>Project and environment</h2>
          <dl className="configuration-summary">
            <div className="row"><dt>Project</dt><dd>{catalog?.projects.find((project) => project.path === current.projectPath)?.name || (current.projectPath ? current.projectPath.split("/").filter(Boolean).at(-1) : "Not selected")}</dd></div>
            <div className="row"><dt>Source metadata</dt><dd>{mode === "lean" ? files ? files.files.length + " Lean files found" : fileLoading ? "Reading…" : "Not read" : "Statement will be translated"}</dd></div>
            <div className="row"><dt>Toolchain check</dt><dd>Not executed</dd></div>
            <div className="row"><dt>Provider</dt><dd>{translateOnly ? "OpenAI translation" : selectedProvider?.label || current.prover || "Not selected"}</dd></div>
            <div className="row"><dt>Output directory</dt><dd>Allocated when this run starts</dd></div>
          </dl>
          <p className="hint">Project discovery reads metadata. Starting a run executes the selected Lake project and may make paid provider requests.</p>
        </section>
        <section className="panel"><h2>Launch configuration</h2>
          <dl className="configuration-summary">
            <div className="row"><dt>Work</dt><dd>{translateOnly ? "Translation only" : mode === "lean" ? drafts.lean.theorem || "Choose a theorem" : "Translation and proof search"}</dd></div>
            {!translateOnly ? <><div className="row"><dt>Prover model</dt><dd>{current.proverModel || (usesCliModel(current.prover) ? "CLI default" : "Not selected")}</dd></div>
              <div className="row"><dt>Refiner</dt><dd>{profile.customRefiner ? profile.refiner + (profile.refinerModel ? " · " + profile.refinerModel : " · CLI default") : "Omitted · CLI default"}</dd></div>
              {explicitOptions.map(([key, value]) => <div className="row" key={key}><dt>{fields.find((field) => field.key === key)?.label || key}</dt><dd>{value}</dd></div>)}
              {!explicitOptions.length ? <div className="row"><dt>Search and budgets</dt><dd>Omitted · CLI defaults</dd></div> : null}
            </> : null}
          </dl>
          {!translateOnly && explicitOptions.length ? <button type="button" className="text-button" onClick={() => changeProfile({ ...profile, options: {} })}>Reset launch settings</button> : null}
          <div className="composer-actions"><button type="submit" className="button button-primary" disabled={readinessIssues.length > 0 || busy}>{busy ? "Starting…" : "Start"}</button><button type="button" className="button" onClick={onLibrary}>Results</button></div>
          {notice ? <p className="notice" role="status">{notice}</p> : null}
          <p className="hint">Closing this page leaves the run active. Stop it from the run workspace.</p>
        </section>
        <p className="meta">Notes-to-project and open-ended research are not available in this interface.</p>
      </aside>
    </form>
  </section>;
}
