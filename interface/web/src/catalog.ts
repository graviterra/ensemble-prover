export type CatalogProject = { path: string; name: string };
export type CatalogProvider = { id: string; label: string; models: string[]; available: boolean; availability: string };
export type CatalogDeployment = { id: string; model: string; contextTokens: number; maxOutputTokens: number; tools: string; reasoningMode: string; reasoningEffort: string; outputLimitIncludesReasoning: string; execution: string; dialect: string; capability: "declared"; probed: false; availability: string };
export type CatalogFile = { path: string; name: string };
export type Catalog = { projects: CatalogProject[]; providers: CatalogProvider[]; deployments: CatalogDeployment[]; roots: CatalogProject[]; control: boolean };
export type ProjectFiles = { path: string; name: string; files: CatalogFile[]; truncated: boolean };
export type Theorems = { theorems: { name: string; statement: string }[]; truncated: boolean; notice?: string };
export type Directory = { path: string; parent: string | null; directories: (CatalogProject & { isProject: boolean })[]; isProject: boolean; truncated?: boolean };
export type OptionField = { key: string; label: string; kind: "number" | "select" | "boolean"; group: string; choices?: string[]; help: string; min?: number; step?: number | "any" };

function object(value: unknown): Record<string, unknown> {
  if (!value || typeof value !== "object" || Array.isArray(value)) throw new Error("The service returned unusable project choices.");
  return value as Record<string, unknown>;
}

function string(value: unknown): string { return typeof value === "string" ? value : ""; }

function list(value: unknown): Record<string, unknown>[] {
  if (!Array.isArray(value)) throw new Error("The service returned unusable project choices.");
  return value.map(object);
}

function paths(value: unknown): CatalogProject[] {
  return list(value).map((item) => ({ path: string(item.path), name: string(item.name) })).filter((item) => item.path);
}

async function read(path: string, signal?: AbortSignal): Promise<Record<string, unknown>> {
  const response = await fetch(path, { signal, cache: "no-store", headers: { Accept: "application/json" } });
  if (response.status === 400) {
    let message = "";
    try {
      const body = object(await response.json());
      if (typeof body.error === "string" && body.error.length <= 240) message = body.error;
    } catch { /* A malformed error still gets an actionable fallback. */ }
    throw new Error(message || "This selection could not be read. Choose another file or folder.");
  }
  if (!response.ok) throw new Error(response.status === 403
    ? "This folder is outside the locations shared by the local service. Choose one of the listed locations."
    : response.status === 404 ? "This file or folder is no longer available. Choose another one."
    : "The local service could not load these choices. Try again.");
  return object(await response.json());
}

export function catalogError(error: unknown): string {
  return error instanceof Error && error.message ? error.message : "Could not load project choices.";
}

export function usesCliModel(provider: string): boolean { return provider === "codex" || provider === "claude-code"; }
export function usesDeployment(provider: string): boolean { return provider === "local"; }
export function requiresExactModel(provider: string): boolean { return provider === "cursor"; }

function finite(value: unknown): number { return typeof value === "number" && Number.isFinite(value) ? value : 0; }

function deployment(item: Record<string, unknown>): CatalogDeployment | null {
  const id = string(item.id);
  const row: CatalogDeployment = {
    id, model: string(item.model), contextTokens: finite(item.contextTokens), maxOutputTokens: finite(item.maxOutputTokens),
    tools: string(item.tools), reasoningMode: string(item.reasoningMode), reasoningEffort: string(item.reasoningEffort),
    outputLimitIncludesReasoning: string(item.outputLimitIncludesReasoning), execution: string(item.execution),
    dialect: string(item.dialect), capability: "declared", probed: false,
    availability: string(item.availability) || "Declared in the operator profile and not probed.",
  };
  if (!/^[A-Za-z_][A-Za-z0-9_-]{0,63}$/.test(id) || !row.model || row.model.length > 512
      || !Number.isSafeInteger(row.contextTokens) || row.contextTokens <= 0
      || !Number.isSafeInteger(row.maxOutputTokens) || row.maxOutputTokens <= 0
      || !["operator_asserted_local", "hosted_upstream", "unknown"].includes(row.execution)
      || JSON.stringify(row).includes("://")) return null;
  return row;
}

export async function fetchCatalog(signal?: AbortSignal): Promise<Catalog> {
  const body = await read("/api/catalog", signal);
  return {
    projects: paths(body.projects), roots: paths(body.roots), control: body.control === true,
    deployments: Array.isArray(body.deployments) ? list(body.deployments).map(deployment).filter((item): item is CatalogDeployment => item !== null) : [],
    providers: list(body.providers).map((item) => ({
      id: string(item.id), label: string(item.label),
      models: Array.isArray(item.models) ? item.models.filter((model): model is string => typeof model === "string" && Boolean(model)) : [],
      available: item.available === true, availability: string(item.availability),
    })).filter((item) => item.id),
  };
}

export async function fetchProject(path: string, signal?: AbortSignal): Promise<ProjectFiles> {
  const body = await read("/api/project?" + new URLSearchParams({ path }), signal);
  return { path: string(body.path), name: string(body.name), files: paths(body.files), truncated: body.truncated === true };
}

export async function fetchTheorems(project: string, file: string, signal?: AbortSignal): Promise<Theorems> {
  const body = await read("/api/theorems?" + new URLSearchParams({ project, file }), signal);
  return {
    theorems: list(body.theorems).map((item) => ({ name: string(item.name), statement: string(item.statement) })).filter((item) => item.name),
    truncated: body.truncated === true, notice: string(body.notice),
  };
}

export async function fetchDirectory(path: string, signal?: AbortSignal): Promise<Directory> {
  const body = await read("/api/browse?" + new URLSearchParams({ path }), signal);
  return {
    path: string(body.path), parent: typeof body.parent === "string" ? body.parent : null, isProject: body.isProject === true, truncated: body.truncated === true,
    directories: list(body.directories).map((item) => ({ path: string(item.path), name: string(item.name), isProject: item.isProject === true })).filter((item) => item.path),
  };
}

export async function fetchOptions(signal?: AbortSignal): Promise<OptionField[]> {
  const body = await read("/api/options", signal);
  return list(body.fields).map((item) => {
    if (item.kind !== "number" && item.kind !== "select" && item.kind !== "boolean") throw new Error("The service returned an unknown launch setting.");
    return {
      key: string(item.key), label: string(item.label), kind: item.kind, group: string(item.group), help: string(item.help),
      choices: Array.isArray(item.choices) ? item.choices.filter((choice): choice is string => typeof choice === "string") : undefined,
      min: typeof item.min === "number" ? item.min : undefined,
      step: typeof item.step === "number" || item.step === "any" ? item.step : undefined,
    };
  });
}
