import type { OptionField } from "../catalog";

export type LaunchProfile = { options: Record<string, string>; refiner: string; refinerModel: string; refinerDeployment: string; customRefiner: boolean; inferencePolicy: string };
const PROFILE_KEY = "ensemble-prover.launch-profile";
const SECRET_KEY = /api[-_ ]?key|secret|token|password|authorization|base[-_ ]?url|config[-_ ]?path/i;

function publicOptions(value: unknown): Record<string, string> {
  if (!value || typeof value !== "object" || Array.isArray(value)) return {};
  return Object.fromEntries(Object.entries(value).filter((entry): entry is [string, string] =>
    entry[0] !== "inference-policy" && !SECRET_KEY.test(entry[0]) && typeof entry[1] === "string" && !entry[1].includes("://") && !/[\\/\0]/.test(entry[1])));
}

function publicText(value: unknown): string {
  if (typeof value !== "string" || value.includes("://") || value.includes("..") || value.includes("\0")) return "";
  return value;
}

export function loadProfile(): LaunchProfile {
  const empty = { options: {}, refiner: "", refinerModel: "", refinerDeployment: "", customRefiner: false, inferencePolicy: "" };
  try {
    const raw: unknown = JSON.parse(localStorage.getItem(PROFILE_KEY) || "null");
    if (!raw || typeof raw !== "object" || Array.isArray(raw)) return empty;
    const row = raw as Record<string, unknown>;
    const options = publicOptions(row.options);
    const legacyOptions = row.options && typeof row.options === "object" && !Array.isArray(row.options) ? row.options as Record<string, unknown> : {};
    const policy = publicText(row.inferencePolicy) || publicText(legacyOptions["inference-policy"]);
    return { options, refiner: publicText(row.refiner), refinerModel: publicText(row.refinerModel), refinerDeployment: publicText(row.refinerDeployment), customRefiner: row.customRefiner === true, inferencePolicy: policy === "mixed" || policy === "local-only" ? policy : "" };
  } catch { return empty; }
}

export function saveProfile(profile: LaunchProfile): void {
  try { localStorage.setItem(PROFILE_KEY, JSON.stringify(loadProfileShape(profile))); } catch { /* The current page retains the settings. */ }
}

function loadProfileShape(profile: LaunchProfile): LaunchProfile {
  return { options: publicOptions(profile.options), refiner: publicText(profile.refiner), refinerModel: publicText(profile.refinerModel), refinerDeployment: publicText(profile.refinerDeployment), customRefiner: profile.customRefiner === true, inferencePolicy: profile.inferencePolicy === "mixed" || profile.inferencePolicy === "local-only" ? profile.inferencePolicy : "" };
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
  const visible = fields.filter((item) => item.key !== "inference-policy");
  const groups = [...new Set(visible.map((item) => item.group))];
  return <>{groups.map((group) => <section className="panel launch-options" key={group}>
    <h2>{group}</h2><p className="meta">Blank settings use the command's defaults. Only your explicit choices are sent.</p>
    <div className="fields split">{visible.filter((item) => item.group === group).map((field) => <label className="field" key={field.key} htmlFor={`option-${field.key}`}>
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
