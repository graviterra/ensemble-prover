import { useEffect, useState } from "react";
import type { FormEvent } from "react";
import { loadSetup, saveSetup } from "../storage";
import { ModelPicker } from "../components/ModelPicker";
import { ProjectPicker } from "../components/ProjectPicker";
import { useCatalog } from "../components/useCatalog";

export function SetupScreen() {
  const [setup, setSetup] = useState(loadSetup);
  const [notice, setNotice] = useState("");
  const { catalog, error, loading, retry } = useCatalog();
  useEffect(() => {
    if (catalog?.projects.length === 1) setSetup((current) => ({ ...current, projectPath: current.projectPath || catalog.projects[0].path }));
  }, [catalog]);

  function save(event: FormEvent) {
    event.preventDefault();
    try { saveSetup(setup); setNotice("Saved in this browser. Empty fields in new work will use these defaults."); }
    catch { setNotice("This browser could not keep the defaults."); }
  }

  return <section className="composer">
    <h1 className="page-title">Workspace setup</h1>
    <p className="lede">Choose a project and prover once, then reuse them for your next run.</p>
    {loading ? <p role="status">Discovering projects and providers…</p> : null}
    {error ? <div role="alert" className="notice"><p>{error}</p><button type="button" className="button" onClick={retry}>Retry discovery</button></div> : null}
    <div className="setup-grid launcher-layout">
      <form className="column" onSubmit={save}>
        <section className="panel"><h2>Default project</h2>
          <ProjectPicker value={setup.projectPath} projects={catalog?.projects ?? []} roots={catalog?.roots ?? []} onChange={(projectPath) => { setSetup((current) => ({ ...current, projectPath })); setNotice(""); }} />
        </section>
        <section className="panel"><h2>Default prover</h2>
          <ModelPicker id="setup" providers={catalog?.providers ?? []} deployments={catalog?.deployments ?? []} provider={setup.prover} model={setup.proverModel} deployment={setup.proverDeployment ?? ""} onChange={(prover, proverModel, proverDeployment = "") => { setSetup((current) => ({ ...current, prover, proverModel: prover === "local" ? "" : proverModel, proverDeployment: prover === "local" ? proverDeployment : "" })); setNotice(""); }} />
          <div className="composer-actions"><button type="submit" className="button button-primary">Save defaults</button></div>
          {notice ? <p role="status">{notice}</p> : null}
        </section>
      </form>
      <aside className="column">
        <section className="panel"><h2>Provider availability</h2>
          <p className="meta">These checks report credentials or installed tools. They do not make a provider request or verify account access.</p>
          <dl className="configuration-summary">{catalog?.providers.map((provider) => <div className="row" key={provider.id}><dt>{provider.label}</dt><dd>{provider.availability}</dd></div>)}</dl>
          <p className="hint">API keys remain in the service environment. This page does not request or display them.</p>
        </section>
        <section className="panel"><h2>Browser preferences</h2>
          <p>Project and prover choices stay in this browser. Existing drafts keep their own settings.</p>
          <p className="meta">Search limits, reasoning, and refiner choices are set in the Launcher. The launch summary shows every explicit override.</p>
          <button type="button" className="button" onClick={retry}>Refresh discovery</button>
        </section>
      </aside>
    </div>
  </section>;
}
