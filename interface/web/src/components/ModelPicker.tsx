import { useEffect } from "react";
import { usesCliModel } from "../catalog";
import type { CatalogProvider } from "../catalog";

export function ModelPicker({ id, providers, provider, model, onChange, error }: {
  id: string; providers: CatalogProvider[]; provider: string; model: string;
  onChange: (provider: string, model: string) => void; error?: string;
}) {
  const selected = providers.find((item) => item.id === provider);
  useEffect(() => {
    if (!provider) {
      const ready = providers.filter((item) => item.available);
      if (ready.length === 1) onChange(ready[0].id, !usesCliModel(ready[0].id) && ready[0].models.length === 1 ? ready[0].models[0] : "");
    } else if (!model && selected?.models.length === 1 && !usesCliModel(provider)) {
      onChange(provider, selected.models[0]);
    }
  }, [providers, provider, model, selected, onChange]);
  return <div className="model-picker">
    <div className="split">
      <label className="field" htmlFor={`${id}-provider`}>
        <span>Provider</span>
        <select id={`${id}-provider`} value={provider} onChange={(event) => {
          const next = providers.find((item) => item.id === event.target.value);
          onChange(event.target.value, !usesCliModel(event.target.value) && next?.models.length === 1 ? next.models[0] : "");
        }}>
          <option value="">Choose a provider</option>
          {provider && !selected ? <option value={provider}>{provider} (saved)</option> : null}
          {providers.map((item) => <option value={item.id} key={item.id}>{item.label}{item.available ? "" : " · needs setup"}</option>)}
        </select>
      </label>
      <label className="field" htmlFor={`${id}-model`}>
        <span>Model</span>
        <select id={`${id}-model`} value={model} disabled={!provider} onChange={(event) => onChange(provider, event.target.value)}>
          <option value="">{usesCliModel(provider) ? "CLI default" : "Choose a model"}</option>
          {model && !selected?.models.includes(model) ? <option value={model}>{model} (saved)</option> : null}
          {selected?.models.map((item) => <option value={item} key={item}>{item}</option>)}
        </select>
      </label>
    </div>
    {selected ? <p className={`provider-status ${selected.available ? "is-ready" : "needs-setup"}`}>{selected.availability}</p> : null}
    {error ? <p className="field-error" role="alert">{error}</p> : null}
    <details className="advanced-fields"><summary>Custom provider or model</summary>
      <p className="meta">Use an installed provider and a model supported by your account. Credentials stay in the service environment.</p>
      <div className="split">
        <label className="field"><span>Provider identifier</span><input value={provider} onChange={(event) => onChange(event.target.value, "")} spellCheck={false} /></label>
        <label className="field"><span>Model identifier</span><input value={model} onChange={(event) => onChange(provider, event.target.value)} spellCheck={false} /></label>
      </div>
    </details>
  </div>;
}
