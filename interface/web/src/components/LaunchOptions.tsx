import type { OptionField } from "../catalog";

export type LaunchProfile = { options: Record<string, string>; refiner: string; refinerModel: string; customRefiner: boolean };
const PROFILE_KEY = "ensemble-prover.launch-profile";

export function loadProfile(): LaunchProfile {
  const empty = { options: {}, refiner: "", refinerModel: "", customRefiner: false };
  try {
    const raw: unknown = JSON.parse(localStorage.getItem(PROFILE_KEY) || "null");
    if (!raw || typeof raw !== "object" || Array.isArray(raw)) return empty;
    const row = raw as Record<string, unknown>;
    const options = row.options && typeof row.options === "object" && !Array.isArray(row.options)
      ? Object.fromEntries(Object.entries(row.options).filter((entry): entry is [string, string] => typeof entry[1] === "string")) : {};
    return { options, refiner: typeof row.refiner === "string" ? row.refiner : "", refinerModel: typeof row.refinerModel === "string" ? row.refinerModel : "", customRefiner: row.customRefiner === true };
  } catch { return empty; }
}

export function saveProfile(profile: LaunchProfile): void {
  try { localStorage.setItem(PROFILE_KEY, JSON.stringify(profile)); } catch { /* The current page retains the settings. */ }
}

export function optionPayload(values: Record<string, string>, fields: OptionField[]): Record<string, string | number | boolean> {
  return Object.fromEntries(Object.entries(values).filter(([, value]) => value !== "").map(([key, value]) => {
    const field = fields.find((item) => item.key === key);
    if (!field) throw new Error("A saved launch setting is unavailable. Reset the launch settings or retry loading them.");
    if (field.kind === "number") {
      if (!value.trim() || !Number.isFinite(Number(value))) throw new Error(`${field.label} must be a finite number.`);
      const number = Number(value);
      if (field.min !== undefined && number < field.min) throw new Error(`${field.label} must be at least ${field.min}.`);
      if (field.step === 1 && !Number.isInteger(number)) throw new Error(`${field.label} must use increments of 1.`);
      return [key, number];
    }
    if (field.kind === "boolean") {
      if (value !== "true" && value !== "false") throw new Error(`${field.label} needs an on or off choice.`);
      return [key, value === "true"];
    }
    if (!field.choices?.includes(value)) throw new Error(`${field.label} has an unavailable choice.`);
    return [key, value];
  }));
}

export function LaunchOptions({ fields, values, onChange }: { fields: OptionField[]; values: Record<string, string>; onChange: (next: Record<string, string>) => void }) {
  const groups = [...new Set(fields.map((item) => item.group))];
  return <>{groups.map((group) => <section className="panel launch-options" key={group}>
    <h2>{group}</h2><p className="meta">Blank settings use the command's defaults. Only your explicit choices are sent.</p>
    <div className="fields split">{fields.filter((item) => item.group === group).map((field) => <label className="field" key={field.key} htmlFor={`option-${field.key}`}>
      <span id={`label-${field.key}`}>{field.label}</span>
      {/* Preserve unfinished numbers so an invalid override cannot become an omitted default. */}
      {field.kind === "number" ? <input id={`option-${field.key}`} type="text" inputMode={field.step === 1 ? "numeric" : "decimal"} spellCheck={false} placeholder="CLI default" value={values[field.key] ?? ""} aria-labelledby={`label-${field.key}`} aria-describedby={`help-${field.key}`} onChange={(event) => onChange({ ...values, [field.key]: event.target.value })} />
        : <select id={`option-${field.key}`} value={values[field.key] ?? ""} aria-labelledby={`label-${field.key}`} aria-describedby={`help-${field.key}`} onChange={(event) => onChange({ ...values, [field.key]: event.target.value })}>
          <option value="">CLI default (not overridden)</option>
          {field.kind === "boolean" ? <><option value="true">On</option><option value="false">Off</option></> : field.choices?.map((choice) => <option value={choice} key={choice}>{choice}</option>)}
        </select>}
      <span className="hint" id={`help-${field.key}`}>{field.help}</span>
    </label>)}</div>
  </section>)}</>;
}
