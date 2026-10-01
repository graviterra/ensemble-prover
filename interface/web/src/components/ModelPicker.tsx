import { useEffect } from "react";
import { requiresExactModel, usesCliModel, usesDeployment } from "../catalog";
import type { CatalogDeployment, CatalogProvider } from "../catalog";

export function ModelPicker({ id, providers, deployments = [], provider, model, deployment = "", onChange, error, autoSelect = true, labels }: {
  id: string; providers: CatalogProvider[]; deployments?: CatalogDeployment[]; provider: string; model: string; deployment?: string;
  onChange: (provider: string, model: string, deployment?: string) => void; error?: string; autoSelect?: boolean;
  labels?: { provider?: string; model?: string; deployment?: string };
}) {
  const selected = providers.find((item) => item.id === provider);
  const selectedDeployment = deployments.find((item) => item.id === deployment);
  const providerLabel = labels?.provider ?? "Provider";
  const modelLabel = labels?.model ?? (requiresExactModel(provider) ? "Exact model name" : "Model");
  const deploymentLabel = labels?.deployment ?? "Deployment";
  useEffect(() => {
    if (!autoSelect) return;
    if (!provider) {
      const ready = providers.filter((item) => item.available);
      if (ready.length === 1) {
        const next = ready[0];
        const nextDeployment = usesDeployment(next.id) && deployments.length === 1 ? deployments[0].id : "";
        const nextModel = usesDeployment(next.id) || requiresExactModel(next.id) || usesCliModel(next.id) ? "" : next.models.length === 1 ? next.models[0] : "";
        if (nextDeployment) onChange(next.id, nextModel, nextDeployment);
        else onChange(next.id, nextModel);
      }
    } else if (usesDeployment(provider) && !deployment && deployments.length === 1) {
      onChange(provider, "", deployments[0].id);
    } else if (!model && selected?.models.length === 1 && !usesCliModel(provider) && !usesDeployment(provider) && !requiresExactModel(provider)) {
      onChange(provider, selected.models[0]);
    }
  }, [autoSelect, providers, deployments, provider, model, deployment, selected, onChange]);
  function chooseProvider(nextId: string) {
    const next = providers.find((item) => item.id === nextId);
    const nextDeployment = usesDeployment(nextId) && deployments.length === 1 ? deployments[0].id : "";
    const nextModel = !next || usesDeployment(nextId) || requiresExactModel(nextId) || usesCliModel(nextId) ? "" : next.models.length === 1 ? next.models[0] : "";
    if (nextDeployment) onChange(nextId, nextModel, nextDeployment);
    else onChange(nextId, nextModel);
  }
  return <div className="model-picker">
    <div className="split">
      <label className="field" htmlFor={`${id}-provider`}><span>{providerLabel}</span>
        <select id={`${id}-provider`} value={provider} onChange={(event) => chooseProvider(event.target.value)}>
          <option value="">Choose a provider</option>
          {provider && !selected ? <option value={provider}>{provider} (saved)</option> : null}
          {providers.map((item) => <option value={item.id} key={item.id}>{item.label}{item.available ? "" : " · needs setup"}</option>)}
        </select>
      </label>
      {usesDeployment(provider) ? <label className="field" htmlFor={`${id}-deployment`}><span>{deploymentLabel}</span>
        <select id={`${id}-deployment`} value={deployment} onChange={(event) => onChange(provider, "", event.target.value)}>
          <option value="">Choose a deployment</option>
          {deployment && !deployments.some((item) => item.id === deployment) && !deployment.includes("://") ? <option value={deployment}>{deployment} (saved)</option> : null}
          {deployments.map((item) => <option value={item.id} key={item.id}>{item.id}</option>)}
        </select>
      </label> : requiresExactModel(provider) ? <label className="field" htmlFor={`${id}-model`}><span>{modelLabel}</span>
        <input id={`${id}-model`} value={model} spellCheck={false} autoComplete="off" onChange={(event) => onChange(provider, event.target.value, "")} />
      </label> : <label className="field" htmlFor={`${id}-model`}><span>{modelLabel}</span>
        <select id={`${id}-model`} value={model} disabled={!provider} onChange={(event) => onChange(provider, event.target.value, deployment)}>
          <option value="">{usesCliModel(provider) ? "CLI default" : "Choose a model"}</option>
          {model && !selected?.models.includes(model) ? <option value={model}>{model} (saved)</option> : null}
          {selected?.models.map((item) => <option value={item} key={item}>{item}</option>)}
        </select>
      </label>}
    </div>
    {usesDeployment(provider) ? <p className="meta">Declared model {selectedDeployment?.model || "follows the selected deployment"}. A model override is not sent.</p> : null}
    {selected ? <p className={`provider-status ${selected.available ? "is-ready" : "needs-setup"}`}>{selected.availability}</p> : null}
    {error ? <p className="field-error" role="alert">{error}</p> : null}
    {usesDeployment(provider) || requiresExactModel(provider) ? null : <details className="advanced-fields"><summary>Custom provider or model</summary>
      <p className="meta">Use an installed provider and a model supported by your account. Credentials stay in the service environment.</p>
      <div className="split">
        <label className="field"><span>Provider identifier</span><input value={provider} onChange={(event) => onChange(event.target.value, "", "")} spellCheck={false} /></label>
        <label className="field"><span>Model identifier</span><input value={model} onChange={(event) => onChange(provider, event.target.value, deployment)} spellCheck={false} /></label>
      </div>
    </details>}
  </div>;
}
