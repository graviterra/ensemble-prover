/** Advisory historical reports. Parsing never reconstructs proof authority. */
export type MemoryRow = {
  id: string; event_id: string; candidate_id: string; name: string; statement: string; text: string;
  reason: string; assumptions: string; conditions: string; retry_conditions: string;
  outcome: string; operation: string; direction: string; scope: string; environment_id: string;
  artifact_id: string; evidence_digest: string; evidence_digests: string[]; artifact_available: boolean; freshness: string; partial: boolean;
  statement_truncated: boolean; remaining_goals: string[]; supplied_premises: string[]; consumers: string[];
  instance_ids: string[]; source_instances: string[]; changed_assumptions: string[];
  specialization_links: string[]; intended_consumers: string[]; expected_use: string; observed_use: string;
};
export type MemoryView = {
  mode: string; status: string; goal_id: string; environment_id: string; policy_id: string;
  allocation_id: string; research_allocation_id: string; generation: Record<string, unknown>; scope: string;
  candidates: MemoryRow[]; applications: MemoryRow[]; obstructions: MemoryRow[];
  proposals: MemoryRow[]; notes: MemoryRow[]; omitted: number | null; partial: boolean;
  eligibility_lease_until: number;
};
export type MemoryRequest = { payload: Record<string, string | number>; status: string; detail: string };
const requestStatuses = new Set(["pending", "admitted", "running", "unresolved", "completed", "rejected", "cancelled"]);
const requestKinds = new Set(["pin", "note", "retry", "generalization"]);
export function parseMemoryRequest(value: unknown): MemoryRequest | undefined {
  const row = object(value);
  const source = object(row.payload);
  if (typeof row.status !== "string" || !requestStatuses.has(row.status)
      || typeof source.kind !== "string" || !requestKinds.has(source.kind)
      || typeof source.request_id !== "string" || !/^[a-zA-Z0-9_:.@-]{1,128}$/.test(source.request_id)
      || row.detail !== undefined && (typeof row.detail !== "string" || row.detail.length > 512 || row.detail.includes("\0"))) return undefined;
  const payload: Record<string, string | number> = {};
  for (const key of ["request_id", "kind", "goal_id", "candidate_id", "environment_id", "policy_id", "retry_of", "text", "statement", "allocation_id"]) {
    if (source[key] === undefined) continue;
    const limit = key === "statement" ? 16384 : key === "text" ? 8192 : 128;
    if (typeof source[key] !== "string" || source[key].length > limit || source[key].includes("\0")) return undefined;
    payload[key] = source[key];
  }
  if (source.max_seconds !== undefined) {
    if (typeof source.max_seconds !== "number" || !Number.isFinite(source.max_seconds) || source.max_seconds < 0 || source.max_seconds > 86400) return undefined;
    payload.max_seconds = source.max_seconds;
  }
  return { payload, status: row.status, detail: typeof row.detail === "string" ? row.detail : "" };
}
const groups = ["candidates", "applications", "obstructions", "proposals", "notes"] as const;
function object(value: unknown): Record<string, unknown> {
  return value && typeof value === "object" && !Array.isArray(value) ? value as Record<string, unknown> : {};
}
function text(value: unknown, max = 160): string { return typeof value === "string" ? value.replaceAll("\0", "").slice(0, max) : ""; }
function count(value: unknown): number | null { return typeof value === "number" && Number.isFinite(value) && value >= 0 ? value : null; }
export function parseMemory(value: unknown): MemoryView | undefined {
  const row = object(value);
  if (!Object.keys(row).length) return undefined;
  const result = { mode: text(row.mode), status: text(row.status), goal_id: text(row.goal_id),
    environment_id: text(row.environment_id), policy_id: text(row.policy_id), allocation_id: text(row.allocation_id),
    research_allocation_id: text(row.research_allocation_id),
    scope: text(row.scope), generation: {}, omitted: count(row.omitted), partial: row.partial === true,
    eligibility_lease_until: count(row.eligibility_lease_until) ?? 0,
  } as MemoryView;
  for (const group of groups) {
    result[group] = Array.isArray(row[group]) ? row[group].slice(0, 16).map((value) => {
      const item = object(value);
      const parsed = {} as MemoryRow;
      for (const key of ["id", "event_id", "candidate_id", "name", "outcome", "operation", "direction", "scope", "environment_id", "freshness"] as const) parsed[key] = text(item[key]);
      for (const key of ["statement", "text", "reason", "assumptions", "conditions", "retry_conditions", "expected_use", "observed_use"] as const) parsed[key] = text(item[key], key === "statement" || key === "text" ? 4096 : 1200);
      parsed.artifact_id = typeof item.artifact_id === "string" && /^[a-f0-9]{64}$/.test(item.artifact_id) ? item.artifact_id : "";
      parsed.evidence_digest = typeof item.evidence_digest === "string" && /^[a-f0-9]{64}$/.test(item.evidence_digest) ? item.evidence_digest : "";
      parsed.evidence_digests = Array.isArray(item.evidence_digests) ? item.evidence_digests.slice(0, 16).filter((digest): digest is string => typeof digest === "string" && /^[a-f0-9]{64}$/.test(digest)) : [];
      parsed.artifact_available = !!parsed.artifact_id && item.artifact_available === true;
      parsed.partial = item.partial === true || ["remaining_goals", "supplied_premises", "consumers", "instance_ids", "source_instances", "changed_assumptions", "specialization_links", "intended_consumers"].some((key) => Array.isArray(item[key]) && item[key].length > 16);
      result.partial ||= parsed.partial;
      parsed.statement_truncated = item.statement_truncated === true || typeof item.statement === "string" && item.statement.length > 4096;
      for (const key of ["remaining_goals", "supplied_premises", "consumers", "instance_ids", "source_instances", "changed_assumptions", "specialization_links", "intended_consumers"] as const) parsed[key] = Array.isArray(item[key]) ? item[key].slice(0, 16).map((value) => text(value, 2048)).filter(Boolean) : [];
      return parsed;
    }) : [];
    result.partial ||= Array.isArray(row[group]) && row[group].length > 16;
  }
  return result;
}

export function refreshPausedPermissions(previous: MemoryView | undefined, current: MemoryView): MemoryView {
  if (!previous || previous.policy_id !== current.policy_id || previous.goal_id !== current.goal_id || previous.environment_id !== current.environment_id) {
    return { ...current, candidates: [], applications: [], obstructions: [], proposals: [], notes: [], eligibility_lease_until: 0 };
  }
  const next = { ...previous, eligibility_lease_until: current.eligibility_lease_until, status: current.status, partial: previous.partial || current.partial };
  for (const group of groups) {
    const eligible = new Set(current[group].map((item) => item.event_id));
    next[group] = previous[group].filter((item) => !!item.event_id && eligible.has(item.event_id));
  }
  return next;
}
