import type { GraphNode, RunDetail } from "./types";

export type Tone = "verified" | "progress" | "internal" | "unresolved" | "plain";

export function humanize(value: string): string {
  return value.trim().replace(/[_-]+/g, " ").replace(/\s+/g, " ");
}

export function looksLikeLean(text: string): boolean {
  return /:=|theorem\b|lemma\b|∀|∃|\bfun\b|\bby\b|\bProp\b/.test(text);
}

function normalize(value: string): string {
  return value.trim().toLowerCase().replace(/[\s-]+/g, "_");
}

export function isCertificateState(state: string): boolean {
  const token = normalize(state);
  if (!token) return false;
  if (token.includes("unverified") || token.includes("not_verified") || token.includes("pending") || token.includes("helper")) {
    return false;
  }
  return token === "verified" || token === "verified_export" || token === "export_verified";
}

export function isCertificateLabel(status: string): boolean {
  const token = normalize(status);
  if (!token || token.includes("unverified") || token.includes("helper") || token.includes("pending")) return false;
  return token === "verified_export" || token === "export_verified" || token.endsWith("_verified_export");
}

export function classify(input: {
  exportState?: string;
  internalSolved?: boolean;
  rootStatus?: string;
}): { tone: Tone; mark: string } {
  const exportState = (input.exportState ?? "").trim();
  const root = (input.rootStatus ?? "").trim();
  if (isCertificateState(exportState)) {
    return { tone: "verified", mark: "Verified export" };
  }
  if (exportState === "failed") {
    return {
      tone: "internal",
      mark: input.internalSolved ? "Solved internally / export failed" : "Export failed",
    };
  }
  if (input.internalSolved) {
    return { tone: "internal", mark: "Solved internally / export pending" };
  }
  const hay = `${exportState} ${root}`.toLowerCase();
  if (hay.includes("unresolved")) {
    return { tone: "unresolved", mark: root || "Root unresolved" };
  }
  if (/search|proving|in progress|running|working/.test(hay)) {
    return { tone: "progress", mark: root || exportState || "Searching" };
  }
  if (root) return { tone: "plain", mark: root };
  if (exportState) return { tone: "plain", mark: exportState };
  return { tone: "plain", mark: "Status was not reported" };
}

export function kindWords(kind: string): string {
  const key = kind.trim().toLowerCase();
  const known: Record<string, string> = {
    english: "English or LaTeX",
    lean: "Lean file",
    nl: "English or LaTeX",
    natural: "English or LaTeX",
    notes: "Notes",
    campaign: "Notes",
    question: "Question",
    research: "Question",
  };
  if (known[key]) return known[key];
  if (!key || key.length > 48) return "";
  return kind.trim();
}

export function timeValue(value: number | string | null | undefined): number {
  if (typeof value === "number" && Number.isFinite(value)) return value > 0 && value < 1e12 ? value * 1000 : value;
  if (typeof value === "string" && value.trim()) {
    const numeric = Number(value);
    if (Number.isFinite(numeric) && numeric > 0) return numeric < 1e12 ? numeric * 1000 : numeric;
    const parsed = Date.parse(value);
    if (!Number.isNaN(parsed)) return parsed;
  }
  return 0;
}

export function formatWhen(value: number | string | null): string {
  const ms = timeValue(value);
  if (!ms) return "No write time recorded";
  const date = new Date(ms);
  if (Number.isNaN(date.getTime())) return "No write time recorded";
  return date.toLocaleString(undefined, { dateStyle: "medium", timeStyle: "short" });
}

export function formatElapsed(seconds: number): string {
  if (!Number.isFinite(seconds)) return "";
  const total = Math.max(0, Math.round(seconds));
  if (total < 60) return `${total}s`;
  const minutes = Math.floor(total / 60);
  const remain = total % 60;
  if (minutes < 60) return remain ? `${minutes} min ${remain}s` : `${minutes} min`;
  const hours = Math.floor(minutes / 60);
  const min = minutes % 60;
  return [`${hours} h`, min ? `${min} min` : "", remain ? `${remain}s` : ""].filter(Boolean).join(" ");
}

export type NodeReading = {
  text: string;
  certificate: boolean;
  progress: boolean;
};

function inProgress(status: string): boolean {
  const token = normalize(status);
  return (
    token.includes("in_progress") ||
    /(^|_)(search|searching|open|pending|running|working|proving|active|progress)(_|$)/.test(token)
  );
}

function soundsSuccessful(status: string): boolean {
  const token = normalize(status);
  if (token.includes("proving") || token.includes("progress") || token.includes("unverified")) return false;
  return /(^|_)(verified|accepted|proved|solved|success|complete|done|ok)(_|$)/.test(token);
}

export function nodeRole(index: number): "root" | "helper" {
  return index === 0 ? "root" : "helper";
}

export function nodeWords(status: string, role: "root" | "helper"): NodeReading {
  const raw = status.trim();
  if (isCertificateLabel(raw)) {
    return { text: "Verified export. This is the certificate.", certificate: true, progress: false };
  }
  if (normalize(raw).includes("typecheck")) {
    return { text: "Typecheck. A typecheck is not a proof.", certificate: false, progress: false };
  }
  if (/final/.test(normalize(raw))) {
    return {
      text: `${humanize(raw) || "Finalization"}. A child finalization is not the problem being solved.`,
      certificate: false,
      progress: false,
    };
  }
  if (role === "helper" && normalize(raw) === "recorded") {
    return {
      text: "Recorded helper. This list is not a kernel dependency graph, and it is not a root certificate.",
      certificate: false,
      progress: false,
    };
  }
  if (role === "helper" && (soundsSuccessful(raw) || normalize(raw) === "verified")) {
    return {
      text: "Helper verification. A helper verification is not a root certificate.",
      certificate: false,
      progress: false,
    };
  }
  if (role === "root" && (soundsSuccessful(raw) || normalize(raw) === "verified")) {
    return {
      text: `${humanize(raw)}. Only a verified export is the certificate.`,
      certificate: false,
      progress: false,
    };
  }
  if (raw && inProgress(raw)) {
    return { text: `${humanize(raw)}. Work is still in progress.`, certificate: false, progress: true };
  }
  if (!raw) {
    return role === "helper"
      ? { text: "No status was reported for this helper. This does not solve the problem.", certificate: false, progress: false }
      : { text: "No status was reported for the root. Only a verified export is the certificate.", certificate: false, progress: false };
  }
  if (role === "helper") {
    return { text: `${humanize(raw)}. This does not solve the problem.`, certificate: false, progress: false };
  }
  return { text: humanize(raw), certificate: false, progress: false };
}

export function toNode(value: unknown): GraphNode | null {
  if (typeof value === "string" && value.trim()) {
    const label = value.trim();
    return { id: label, label, status: "" };
  }
  if (!value || typeof value !== "object") return null;
  const row = value as Record<string, unknown>;
  const id = typeof row.id === "string" ? row.id.trim() : "";
  const label = typeof row.label === "string" ? row.label.trim() : "";
  const status = typeof row.status === "string" ? row.status : "";
  if (!id && !label) return null;
  return {
    id: id || label, label: label || id, status,
    kind: row.kind === "root" || row.kind === "helper" ? row.kind : undefined,
    supports: Array.isArray(row.supports) ? row.supports.filter((value): value is string => typeof value === "string") : [],
    recordedAtS: typeof row.recordedAtS === "number" && Number.isFinite(row.recordedAtS) ? row.recordedAtS : null,
  };
}

export function collectNodes(detail: Pick<RunDetail, "graph" | "helpers">): GraphNode[] {
  const graph = detail.graph.map((node) => toNode(node)).filter((node): node is GraphNode => node !== null);
  const extras = nodesFromHelpers(detail.helpers).filter((node) => !graph.some((existing) => existing.id === node.id));
  return [...graph, ...extras];
}

function nodesFromHelpers(helpers: unknown): GraphNode[] {
  if (Array.isArray(helpers)) {
    return helpers.map((item) => toNode(item)).filter((node): node is GraphNode => node !== null);
  }
  return [];
}

export function helperSummary(helpers: unknown): string | null {
  if (helpers == null) return null;
  if (typeof helpers === "number" && Number.isFinite(helpers)) {
    return `Helpers recorded: ${helpers}. A helper verification is not a root certificate.`;
  }
  if (typeof helpers === "string" && helpers.trim()) {
    return `${helpers.trim()}. A helper verification is not a root certificate.`;
  }
  if (Array.isArray(helpers)) {
    if (helpers.length === 0) return null;
    return "Helpers are shown in the graph. A helper verification is not a root certificate.";
  }
  if (typeof helpers === "object") {
    return "Helpers were returned with this attempt. A helper verification is not a root certificate.";
  }
  return null;
}

export function processWords(status: string, detail: string): { text: string; progress: boolean } {
  const key = status.trim().toLowerCase();
  const known: Record<string, string> = {
    referenced: "A process is referenced for this attempt.",
    none_found: "No process was found for this attempt.",
    unknown: "It is unknown whether a process is still running.",
    running: "Work is in progress.",
    stopping: "An interrupt is underway.",
    stopped: "The process has stopped.",
    exited: "The process has finished.",
    dead: "The process is no longer running.",
    idle: "Nothing is running right now.",
  };
  const lead = known[key] ?? (key ? `Process status: ${humanize(status)}.` : "No process status was returned.");
  const extra = safeProse(detail);
  const progress = key === "running" || key === "stopping" || /search|progress|proving|working/.test(key);
  return { text: extra ? `${lead} ${extra}` : lead, progress };
}

export function safeProse(detail: string): string {
  const trimmed = detail.trim();
  if (!trimmed || trimmed.length > 400) return "";
  if (/argv|python\s+-m|\/bin\/|traceback|\bargs\b|\bcommand\b|\bshell\b/i.test(trimmed)) return "";
  return trimmed;
}

function fieldKind(key: string): "unpriced" | "money" | "other" {
  if (/unpriced/i.test(key)) return "unpriced";
  if (/cost|spend|priced|price|usage/i.test(key)) return "money";
  return "other";
}

function scrubZeroMoney(text: string): string {
  const trimmed = text.trim();
  if (/^\$?\s*0+(?:\.0+)?$/.test(trimmed)) return "unpriced";
  return trimmed.replace(/\$\s*0+(?:\.0+)?(?![\d.])/g, "unpriced");
}

function labelize(key: string): string {
  const spaced = key.replace(/([a-z])([A-Z])/g, "$1 $2").replace(/[_-]+/g, " ").replace(/text$/i, "").trim();
  if (!spaced) return "Spend";
  return spaced.charAt(0).toUpperCase() + spaced.slice(1);
}

function pushSpend(lines: string[], key: string, value: unknown, depth: number): void {
  if (value == null || depth > 3) return;
  const kind = fieldKind(key);
  if (typeof value === "string") {
    const text = kind === "unpriced" || kind === "money" ? scrubZeroMoney(value) : value.trim();
    if (text) lines.push(kind === "unpriced" && !/unpriced/i.test(text) ? `${text} unpriced` : text);
    return;
  }
  if (typeof value === "number") {
    if (!Number.isFinite(value)) return;
    if (kind === "unpriced") {
      lines.push(`${value} unpriced`);
      return;
    }
    if (kind === "money" && value === 0) {
      lines.push("unpriced");
      return;
    }
    lines.push(`${labelize(key)}: ${value}`);
    return;
  }
  if (typeof value === "boolean") return;
  if (Array.isArray(value)) {
    for (const item of value) pushSpend(lines, key, item, depth + 1);
    return;
  }
  if (typeof value === "object") {
    for (const [childKey, child] of Object.entries(value as Record<string, unknown>)) {
      pushSpend(lines, childKey, child, depth + 1);
    }
  }
}

export function spendLines(costFields: Record<string, unknown>): string[] {
  const lines: string[] = [];
  for (const [key, value] of Object.entries(costFields)) pushSpend(lines, key, value, 0);
  const unique = [...new Set(lines.map((line) => line.trim()).filter(Boolean))];
  if (unique.length === 0) return ["No spend figure was returned."];
  return unique.slice(0, 8).map((line) => (/^\$\s*0+(?:\.0+)?$/.test(line) ? "unpriced" : line));
}

const SERVICE_MESSAGES: Record<string, string> = {
  not_found: "That attempt is not in the library.",
  not_owned: "That attempt is not owned by this service, so it cannot be changed here.",
  not_owned_or_control_disabled: "This service is not allowing that for this attempt.",
  launch_failed: "That attempt could not be started. Its storage and execution are uncertain.",
  registry_state_unavailable: "Saved launch state cannot be read or updated safely.",
  memory_unavailable: "Mathematical memory is unavailable for this attempt right now.",
  memory_request_unavailable_or_conflicting: "That memory request could not be recorded; it may conflict with an earlier request.",
  evidence_unavailable: "That evidence copy is unavailable right now.",
  invalid_evidence_reference: "That evidence reference was not valid.",
  host_rejected: "The request was not accepted from this address.",
  origin_rejected: "The request was not accepted from this page.",
};

export function publicMessage(status: number, code: string, raw: string, action: "start" | "stop" | "read"): string {
  if (code === "csrf_rejected") return "The local session changed. Try again.";
  if (code === "confirmation_rejected") {
    return "That confirmation expired. Stop was not sent.";
  }
  if (code === "control_disabled") {
    if (action === "start") return "Starting work is turned off on this service";
    if (action === "stop") return "Stopping is turned off on this service";
    return "This service is not allowing that.";
  }
  const trimmed = raw.trim();
  const token = normalize(code);
  const known = SERVICE_MESSAGES[token];
  if (typeof known === "string" && (!trimmed || normalize(trimmed) === token)) return known;
  if (!trimmed || trimmed.length > 240 || /traceback|python\s+-m|\bargv\b|stack trace|\bcommand\b|\bshell\b/i.test(trimmed)) {
    if (status === 404 && action === "read") return "That attempt is not in the library.";
    return "The service could not complete that.";
  }
  return trimmed;
}
