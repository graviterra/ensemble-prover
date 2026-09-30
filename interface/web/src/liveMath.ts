/** Read-only presentation of bounded, recorded runtime evidence. */
export type MathSelection = {
  approach: string; approachId: string; obligationId: string; statement: string;
  action: string; dispatchId: string; scope: string; elapsedS: number | null;
  status: "selected" | "completed" | "unknown"; reason: string; connection: string;
  workType: string; openRequirements: number | null; statementTruncated: boolean;
};
export type MathReceipt = {
  action: string; dispatchId: string; scope: string; durationS: number | null;
  elapsedS: number | null; result: string; leanStatus: string;
};
export type RuntimeSetting = {
  role: string; model: string; provider: string; reasoning: string; requestedReasoning: string;
  scope: string; requestId: string; transport: string; outputTokens: number | null; source: string; elapsedS: number | null; workType: string;
};
export type LiveMathView = {
  selection: MathSelection | null; activity: MathSelection | null; lastCostlyAction: MathReceipt | null;
  source: { commit: string; dirty: boolean | null; available: boolean; fingerprint: string; partial: boolean };
  settings: RuntimeSetting[];
  health: {
    activeDeferrals: { action: string; reason: string; scope: string }[];
    providerIssues: { role: string; status: string; scope: string; elapsedS: number | null }[];
    backlog: boolean; partialTrace: boolean; stale: boolean; traceAgeS: number | null; traceAvailable: boolean | null;
    processStatus: string; omittedDeferrals: number;
  };
};

function object(value: unknown): Record<string, unknown> {
  return value && typeof value === "object" && !Array.isArray(value) ? value as Record<string, unknown> : {};
}
function text(value: unknown, limit = 512): string {
  return typeof value === "string" ? value.replaceAll("\0", "").slice(0, limit) : "";
}
function scopeText(value: unknown): string {
  const label = text(value).trim();
  return ["not recorded", "unscoped", "unknown"].includes(label.toLowerCase()) ? "" : label;
}
function number(value: unknown): number | null {
  return typeof value === "number" && Number.isFinite(value) && value >= 0 ? value : null;
}
function rows(value: unknown): Record<string, unknown>[] {
  return Array.isArray(value) ? value.slice(0, 16).filter((item) => item && typeof item === "object" && !Array.isArray(item)).map(object) : [];
}
function selection(value: unknown): MathSelection | null {
  const row = object(value);
  if (!Object.keys(row).length) return null;
  return {
    approach: text(row.approach), approachId: text(row.approachId), obligationId: text(row.obligationId),
    statement: text(row.statement, 4096), action: text(row.action), dispatchId: text(row.dispatchId),
    scope: scopeText(row.scope), elapsedS: number(row.elapsedS),
    status: row.status === "selected" || row.status === "completed" ? row.status : "unknown",
    reason: text(row.reason, 800), connection: text(row.connection), workType: text(row.workType),
    openRequirements: number(row.openRequirements), statementTruncated: row.statementTruncated === true || (typeof row.statement === "string" && row.statement.length > 4096),
  };
}
export function parseLiveMath(value: unknown): LiveMathView | undefined {
  const row = object(value);
  if (!Object.keys(row).length) return undefined;
  const source = object(row.source), health = object(row.health), receipt = object(row.lastCostlyAction);
  const commit = typeof source.commit === "string" ? source.commit.slice(0, 65) : "";
  const fingerprint = typeof source.fingerprint === "string" ? source.fingerprint.slice(0, 65) : "";
  const validCommit = /^(?:[a-f0-9]{40}|[a-f0-9]{64})$/i.test(commit);
  const sourceAvailable = source.available === true && validCommit;
  return {
    selection: selection(row.selection), activity: selection(row.activity),
    lastCostlyAction: Object.keys(receipt).length ? {
      action: text(receipt.action), dispatchId: text(receipt.dispatchId), scope: scopeText(receipt.scope),
      durationS: number(receipt.durationS), elapsedS: number(receipt.elapsedS), result: text(receipt.result, 1000), leanStatus: text(receipt.leanStatus),
    } : null,
    source: { commit: validCommit ? commit : "", dirty: sourceAvailable && typeof source.dirty === "boolean" ? source.dirty : null,
      available: sourceAvailable, fingerprint: /^[a-f0-9]{64}$/i.test(fingerprint) ? fingerprint : "", partial: source.partial === true },
    settings: rows(row.settings).map((item) => ({
      role: text(item.role), model: text(item.model), provider: text(item.provider), reasoning: text(item.reasoning),
      requestedReasoning: text(item.requestedReasoning), scope: scopeText(item.scope), requestId: text(item.requestId), transport: text(item.transport), outputTokens: number(item.outputTokens),
      source: text(item.source), elapsedS: number(item.elapsedS), workType: text(item.workType),
    })),
    health: {
      activeDeferrals: rows(health.activeDeferrals).map((item) => ({ action: text(item.action), reason: text(item.reason), scope: scopeText(item.scope) })),
      providerIssues: rows(health.providerIssues).map((item) => ({ role: text(item.role), status: text(item.status), scope: scopeText(item.scope), elapsedS: number(item.elapsedS) })),
      backlog: health.backlog === true, partialTrace: health.partialTrace === true, stale: health.stale === true,
      traceAvailable: typeof health.traceAvailable === "boolean" ? health.traceAvailable : null,
      traceAgeS: number(health.traceAgeS), processStatus: text(health.processStatus), omittedDeferrals: number(health.omittedDeferrals) ?? 0,
    },
  };
}
