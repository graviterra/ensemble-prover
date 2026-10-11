export const tokenFields = ["input_tokens", "output_tokens", "cached_input_tokens", "cache_write_tokens", "reasoning_output_tokens"] as const;
export type TokenTotals = Record<typeof tokenFields[number], number | null>;
export type TokenUsage = {
  totals: TokenTotals | null;
  roles: (TokenTotals & { role: string })[];
  calls: { requestId: string; role: string; scope: string; model: string; status: string; elapsedS: number | null; thinkingBlockTokens: number | null }[];
  reportedReceipts: number; incompleteReceipts: number; incompleteBreakdowns: number; lastUsageS: number | null; partial: boolean; backlog: boolean;
};
const obj = (v: unknown): Record<string, unknown> => v && typeof v === "object" && !Array.isArray(v) ? v as Record<string, unknown> : {};
const text = (v: unknown) => typeof v === "string" && v.length <= 160 && !/[\x00-\x1f\x7f]/.test(v) ? v : "";
const count = (v: unknown) => typeof v === "number" && Number.isSafeInteger(v) && v >= 0 ? v : null;
const seconds = (v: unknown) => typeof v === "number" && Number.isFinite(v) && v >= 0 ? v : null;
const totals = (v: unknown): TokenTotals => Object.fromEntries(tokenFields.map(k => [k, count(obj(v)[k])])) as TokenTotals;

export function parseTokenUsage(value: unknown): TokenUsage | undefined {
  if (!value || typeof value !== "object" || Array.isArray(value)) return undefined;
  const row = obj(value);
  const sums = totals(row.totals);
  return {
    totals: sums.input_tokens !== null || sums.output_tokens !== null ? sums : null,
    roles: (Array.isArray(row.roles) ? row.roles : []).slice(0, 33).map(item => ({ role: text(obj(item).role), ...totals(item) })),
    calls: (Array.isArray(row.calls) ? row.calls : []).slice(0, 64).map(item => {
      const call = obj(item);
      return { requestId: text(call.requestId), role: text(call.role), scope: text(call.scope), model: text(call.model), status: text(call.status), elapsedS: seconds(call.elapsedS), thinkingBlockTokens: count(call.thinkingBlockTokens) };
    }).filter(call => call.requestId),
    reportedReceipts: count(row.reportedReceipts) ?? 0, incompleteReceipts: count(row.incompleteReceipts) ?? 0,
    incompleteBreakdowns: count(row.incompleteBreakdowns) ?? 0,
    lastUsageS: seconds(row.lastUsageS), partial: row.partial === true, backlog: row.backlog === true,
  };
}
