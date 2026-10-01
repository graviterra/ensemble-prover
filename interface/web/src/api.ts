import type { Formalization, GraphNode, Lane, LibraryRun, Milestone, NodeEvidence, RunDetail, StopResult } from "./types";
import { publicMessage, toNode } from "./words";

import { parseLiveMath } from "./liveMath";
import { parseMemory, parseMemoryRequest } from "./memory";
import type { MemoryRequest, MemoryView } from "./memory";

const BLOCKED = new Set(["command", "argv", "args", "shell"]);

export class ApiError extends Error {
  readonly status: number;
  readonly code: string;

  constructor(status: number, message: string, code = "") {
    super(message);
    this.name = "ApiError";
    this.status = status;
    this.code = code;
  }
}

function sanitize(value: unknown): unknown {
  if (Array.isArray(value)) return value.map((item) => sanitize(item));
  if (!value || typeof value !== "object") return value;
  const out: Record<string, unknown> = {};
  for (const [key, child] of Object.entries(value as Record<string, unknown>)) {
    if (BLOCKED.has(key)) continue;
    out[key] = sanitize(child);
  }
  return out;
}

async function readBody(response: Response): Promise<unknown> {
  const text = await response.text();
  if (!text) return null;
  try {
    return JSON.parse(text) as unknown;
  } catch {
    return { error: text.slice(0, 200) };
  }
}

function errorCode(body: unknown): string {
  if (!body || typeof body !== "object") return "";
  const error = (body as Record<string, unknown>).error;
  return typeof error === "string" ? error : "";
}

function asApiError(response: Response, body: unknown, action: "start" | "stop" | "read"): ApiError {
  const code = errorCode(body);
  const row = body && typeof body === "object" ? (body as Record<string, unknown>) : {};
  const raw = typeof row.message === "string"
    ? row.message
    : typeof row.detail === "string"
      ? row.detail
      : code;
  return new ApiError(response.status, publicMessage(response.status, code, raw, action), code);
}

export function failureText(error: unknown, fallback = "The local service did not answer."): string {
  if (error instanceof ApiError) return error.message;
  if (error instanceof DOMException && error.name === "AbortError") return "";
  return fallback;
}

function asBool(value: unknown): boolean {
  return value === true || value === "true" || value === 1;
}

function asCount(value: unknown): number | null {
  if (typeof value === "number" && Number.isFinite(value)) return value;
  if (typeof value === "string" && value.trim() && Number.isFinite(Number(value))) return Number(value);
  return null;
}

function asText(value: unknown): string {
  return typeof value === "string" ? value : "";
}

const COST_KEY = /unpriced|cost|spend|priced|price|usage/i;

function takeCostFields(row: Record<string, unknown>): Record<string, unknown> {
  const cost: Record<string, unknown> = {};
  for (const [key, value] of Object.entries(row)) {
    if (COST_KEY.test(key)) cost[key] = value;
  }
  return cost;
}

function asRun(value: unknown): LibraryRun | null {
  if (!value || typeof value !== "object") return null;
  const row = value as Record<string, unknown>;
  if (typeof row.id !== "string" || !row.id.trim()) return null;
  const stamp = row.lastWriteTs;
  return {
    id: row.id,
    label: asText(row.label),
    kind: asText(row.kind),
    problem: asText(row.problem),
    exportState: asText(row.exportState),
    internalSolved: asBool(row.internalSolved),
    rootStatus: asText(row.rootStatus),
    hasSummary: asBool(row.hasSummary),
    lastWriteTs: typeof stamp === "number" || typeof stamp === "string" ? stamp : null,
    launchId: asText(row.launchId),
    launchStatus: asText(row.launchStatus),
    formalizationStatus: asText(row.formalizationStatus),
  };
}

function asLanes(value: unknown): Lane[] {
  if (!Array.isArray(value)) return [];
  const lanes: Lane[] = [];
  for (const item of value) {
    if (!item || typeof item !== "object") continue;
    const row = item as Record<string, unknown>;
    const name = asText(row.name).trim();
    if (!name) continue;
    lanes.push({ name, count: asCount(row.count) ?? 0, lastText: asText(row.lastText), lastElapsedS: asCount(row.lastElapsedS) });
  }
  return lanes;
}

function asMilestones(value: unknown): Milestone[] {
  if (!Array.isArray(value)) return [];
  const milestones: Milestone[] = [];
  for (const item of value) {
    if (!item || typeof item !== "object") continue;
    const row = item as Record<string, unknown>;
    milestones.push({
      elapsedS: asCount(row.elapsedS) ?? 0,
      text: asText(row.text),
      kind: asText(row.kind),
    });
  }
  return milestones;
}

function asGraph(value: unknown): GraphNode[] {
  if (!Array.isArray(value)) return [];
  return value.map((item) => toNode(item)).filter((node): node is GraphNode => node !== null);
}

function artifactName(value: unknown): string {
  if (typeof value !== "string") return "";
  const name = value.trim();
  if (!name || name.length > 120 || name === "." || name === ".." || /[/\\\0]/.test(name)) return "";
  return name;
}

function asFormalization(value: unknown): Formalization {
  const row = value && typeof value === "object" ? (value as Record<string, unknown>) : {};
  const files = Array.isArray(row.artifactFiles)
    ? row.artifactFiles.map(artifactName).filter((name): name is string => Boolean(name))
    : [];
  return {
    status: asText(row.status),
    statement: asText(row.statement),
    message: asText(row.message),
    leanSource: asText(row.leanSource),
    leanFile: artifactName(row.leanFile),
    artifactFiles: [...new Set(files)],
  };
}

function asNodeEvidence(value: unknown): Record<string, NodeEvidence> {
  if (!value || typeof value !== "object" || Array.isArray(value)) return {};
  const entries: [string, NodeEvidence][] = [];
  let remaining = 1024 * 1024;
  for (const [id, raw] of Object.entries(value).slice(0, 513)) {
    if (!raw || typeof raw !== "object" || Array.isArray(raw) || id.length > 512) continue;
    const row = raw as Record<string, unknown>;
    const text = (key: string, limit: number) => typeof row[key] === "string" && row[key].length <= limit && !row[key].includes("\0") ? row[key] : "";
    const statement = text("statement", 16384), leanSource = text("leanSource", 32768);
    if (statement.length + leanSource.length > remaining) continue;
    remaining -= statement.length + leanSource.length;
    entries.push([id, { statement, leanSource, scope: text("scope", 512), source: text("source", 512), reason: text("reason", 512) }]);
  }
  return Object.fromEntries(entries);
}

export function asDetail(value: unknown): RunDetail {
  const row = value && typeof value === "object" ? (value as Record<string, unknown>) : {};
  const process = row.process && typeof row.process === "object" ? (row.process as Record<string, unknown>) : {};
  return {
    kind: asText(row.kind),
    problem: asText(row.problem),
    exportState: asText(row.exportState),
    exportReason: asText(row.exportReason),
    internalSolved: asBool(row.internalSolved),
    rootStatus: asText(row.rootStatus),
    childRootFinalizations: asCount(row.childRootFinalizations),
    liveMath: parseLiveMath(row.liveMath),
    lastEventS: asCount(row.lastEventS),
    process: { status: asText(process.status), detail: asText(process.detail) },
    lanes: asLanes(row.lanes),
    milestones: asMilestones(row.milestones),
    events: Array.isArray(row.events) ? row.events.slice(-100).flatMap((item: unknown) => {
      if (!item || typeof item !== "object") return [];
      const event = item as Record<string, unknown>;
      return [{ elapsedS: asCount(event.elapsedS) ?? 0, scope: asText(event.scope), kind: asText(event.kind), text: asText(event.text) }];
    }) : [],
    graph: asGraph(row.graph),
    nodeEvidence: asNodeEvidence(row.nodeEvidence),
    helpers: row.helpers,
    costFields: takeCostFields(row),
    launchId: asText(row.launchId),
    launchStatus: asText(row.launchStatus),
    formalization: asFormalization(row.formalization),
  };
}

export function readId(body: unknown): string {
  if (!body || typeof body !== "object") return "";
  const row = body as Record<string, unknown>;
  for (const key of ["id", "runId", "run_id", "attemptId"]) {
    const value = row[key];
    if (typeof value === "string" && value.trim()) return value.trim();
  }
  const nested = row.run ?? row.attempt;
  if (nested && typeof nested === "object") {
    const id = (nested as Record<string, unknown>).id;
    if (typeof id === "string" && id.trim()) return id.trim();
  }
  return "";
}

async function request(path: string, init: RequestInit, action: "start" | "stop" | "read"): Promise<unknown> {
  const response = await fetch(path, { cache: "no-store", ...init });
  const body = await readBody(response);
  if (!response.ok) throw asApiError(response, body, action);
  return body;
}

type Session = { csrfToken: string; control: boolean };

let sessionRequest: Promise<Session> | null = null;

export function clearSessionCache(): void {
  sessionRequest = null;
}

export async function fetchSession(): Promise<Session> {
  if (sessionRequest) return sessionRequest;
  const pending = (async () => {
    const response = await fetch("/api/session", { cache: "no-store", headers: { Accept: "application/json" } });
    const body = await readBody(response);
    if (!response.ok) throw asApiError(response, body, "read");
    const row = body && typeof body === "object" ? (body as Record<string, unknown>) : {};
    const csrfToken = asText(row.csrfToken);
    if (!csrfToken) throw new ApiError(500, "The local session response was not usable.");
    return { csrfToken, control: row.control === true };
  })();
  sessionRequest = pending;
  try {
    return await pending;
  } catch (error) {
    if (sessionRequest === pending) sessionRequest = null;
    throw error;
  }
}

async function mutationResponse(path: string, payload: unknown, signal?: AbortSignal): Promise<{ response: Response; body: unknown }> {
  const serialized = JSON.stringify(sanitize(payload));
  for (let attempt = 0; attempt < 2; attempt += 1) {
    const session = await fetchSession();
    if (signal?.aborted) throw new DOMException("Request aborted", "AbortError");
    const response = await fetch(path, {
      method: "POST",
      cache: "no-store",
      signal,
      headers: {
        Accept: "application/json",
        "Content-Type": "application/json",
        "X-Ensemble-CSRF": session.csrfToken,
      },
      body: serialized,
    });
    const body = await readBody(response);
    if (attempt === 0 && response.status === 403 && errorCode(body) === "csrf_rejected") {
      clearSessionCache();
      continue;
    }
    return { response, body };
  }
  throw new ApiError(403, "The local session changed. Try again.", "csrf_rejected");
}

async function mutation(path: string, payload: unknown, action: "start" | "stop", signal?: AbortSignal): Promise<unknown> {
  const { response, body } = await mutationResponse(path, payload, signal);
  if (!response.ok) throw asApiError(response, body, action);
  return body;
}

export async function fetchMemory(runId: string, signal?: AbortSignal): Promise<MemoryView | undefined> {
  return parseMemory(await request(`/api/memory/${encodeURIComponent(runId)}`, { signal }, "read"));
}
export async function submitMemoryRequest(runId: string, payload: Record<string, string | number>): Promise<MemoryRequest> {
  const body: unknown = await mutation(`/api/memory/${encodeURIComponent(runId)}/requests`, payload, "start");
  const record = parseMemoryRequest(body && typeof body === "object" ? (body as Record<string, unknown>).request : undefined);
  if (!record || record.payload.request_id !== payload.request_id || record.payload.kind !== payload.kind) throw new ApiError(502, "The request receipt was unusable. Its storage and execution are uncertain.", "memory_response_unusable");
  return record;
}
export async function fetchMemoryRequests(runId: string, signal?: AbortSignal): Promise<MemoryRequest[]> {
  const body: unknown = await request(`/api/memory/${encodeURIComponent(runId)}/requests`, { signal }, "read");
  const records = body && typeof body === "object" ? (body as Record<string, unknown>).requests : undefined;
  return Array.isArray(records) ? records.slice(0, 64).map(parseMemoryRequest).filter((record): record is MemoryRequest => !!record) : [];
}
export async function materializeMemoryEvidence(runId: string, eventId: string, digest: string): Promise<string> {
  const body: unknown = await mutation(`/api/memory/${encodeURIComponent(runId)}/evidence`, { event_id: eventId, digest }, "start");
  const artifactId = body && typeof body === "object" ? (body as Record<string, unknown>).artifact_id : undefined;
  if (typeof artifactId !== "string" || !/^[a-f0-9]{64}$/.test(artifactId)) throw new ApiError(502, "The evidence-copy receipt was unusable.", "memory_response_unusable");
  return artifactId;
}

export async function fetchLibrary(signal?: AbortSignal): Promise<LibraryRun[]> {
  const body = await request("/api/library", { signal, headers: { Accept: "application/json" } }, "read");
  if (!body || typeof body !== "object" || !Array.isArray((body as { runs?: unknown }).runs)) {
    throw new ApiError(500, "The library response was not usable.");
  }
  return (body as { runs: unknown[] }).runs.map((item) => asRun(item)).filter((item): item is LibraryRun => item !== null);
}


export async function fetchRun(id: string, signal?: AbortSignal): Promise<RunDetail> {
  const body = await request(`/api/runs/${encodeURIComponent(id)}`, { signal, headers: { Accept: "application/json" } }, "read");
  return asDetail(body);
}

export async function postAttempt(payload: unknown): Promise<unknown> {
  const body = await mutation("/api/attempts", payload, "start");
  if (!readId(body)) {
    throw new ApiError(502, uncertainStartMessage, "start_response_unusable");
  }
  return body;
}

const uncertainStartMessage = "The service did not return a usable attempt identity. Work may have started. Check the library before retrying; the form retains this submission's retry identity.";

export type OptionalStart =
  | { started: true; id: string }
  | { started: false; missing: boolean; message: string; definitiveNoStart?: boolean };

export async function postIfPresent(path: string, payload: unknown): Promise<OptionalStart> {
  let result: { response: Response; body: unknown };
  try {
    result = await mutationResponse(path, payload);
  } catch {
    return {
      started: false,
      missing: false,
      message: "The local service did not answer. Work may have started. Check the library before retrying; the form retains this submission's retry identity.",
    };
  }
  const { response, body } = result;
  if (response.status === 404 || response.status === 405 || response.status === 501) {
    return {
      started: false,
      missing: true,
      message: "This start is saved in the form. The service did not start it.",
    };
  }
  if (!response.ok) {
    const error = asApiError(response, body, "start");
    return {
      started: false,
      missing: false,
      message: error.message,
      ...(error.code === "launch_failed" ? { definitiveNoStart: true } : {}),
    };
  }
  const id = readId(body);
  if (!id) return { started: false, missing: false, message: uncertainStartMessage };
  return { started: true, id };
}

export async function postStop(id: string, confirmToken: string | null, signal?: AbortSignal): Promise<StopResult> {
  const payload = confirmToken ? { confirmToken } : {};
  const body = await mutation(`/api/runs/${encodeURIComponent(id)}/stop`, payload, "stop", signal);
  const row = body && typeof body === "object" ? (body as Record<string, unknown>) : {};
  return {
    signalled: row.signalled === true,
    confirmToken: asText(row.confirmToken),
    detail: asText(row.detail),
  };
}
