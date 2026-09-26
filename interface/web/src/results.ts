import { sweepAttempt } from "./sweeps";
import type { LibraryRun } from "./types";
import { isCertificateState, timeValue } from "./words";

export const resultOutcomes = [
  ["all", "All root outcomes"], ["verified", "Verified export"],
  ["internal", "Internal solve / export pending"], ["export_failed", "Export failed"],
  ["no_solve", "No solve reported"],
] as const;
export type ResultOutcome = typeof resultOutcomes[number][0];
export type ResultsFilters = { query: string; outcome: ResultOutcome; sweep: string; running: boolean; sort: "recent" | "oldest" | "theorem" };

export function defaultResultsFilters(): ResultsFilters {
  return { query: "", outcome: "all", sweep: "", running: false, sort: "recent" };
}

export function normalizeResultsFilters(value: unknown): ResultsFilters {
  const row = value && typeof value === "object" ? value as Record<string, unknown> : {};
  return {
    query: typeof row.query === "string" ? row.query : "",
    sweep: typeof row.sweep === "string" ? row.sweep : "",
    outcome: resultOutcomes.some(([key]) => key === row.outcome) ? row.outcome as ResultOutcome : "all",
    running: row.running === true,
    sort: row.sort === "oldest" || row.sort === "theorem" ? row.sort : "recent",
  };
}

export function resultsToQuery(filters: ResultsFilters): string {
  const query = new URLSearchParams();
  if (filters.query) query.set("q", filters.query);
  if (filters.outcome !== "all") query.set("outcome", filters.outcome);
  if (filters.sweep) query.set("sweep", filters.sweep);
  if (filters.running) query.set("running", "1");
  if (filters.sort !== "recent") query.set("sort", filters.sort);
  return query.toString();
}

export function resultsFromQuery(query: string): ResultsFilters {
  const params = new URLSearchParams(query);
  return normalizeResultsFilters({ query: params.get("q"), outcome: params.get("outcome"), sweep: params.get("sweep"), running: params.get("running") === "1", sort: params.get("sort") });
}

export function resultTitle(run: LibraryRun): string {
  return run.problem.trim() || sweepAttempt(run.id)?.problem || run.label.trim() || run.id;
}

export function resultOutcome(run: LibraryRun): Exclude<ResultOutcome, "all"> {
  if (isCertificateState(run.exportState)) return "verified";
  if (run.exportState.trim().toLowerCase() === "failed") return "export_failed";
  if (run.internalSolved) return "internal";
  return "no_solve";
}

export function filterResults(runs: LibraryRun[], filters: ResultsFilters): LibraryRun[] {
  const needle = filters.query.trim().toLowerCase();
  return runs.filter((run) => (!filters.running || run.launchStatus === "running") &&
    (!filters.sweep || sweepAttempt(run.id)?.sweep === filters.sweep) &&
    (filters.outcome === "all" || resultOutcome(run) === filters.outcome) &&
    (!needle || `${run.problem} ${run.label} ${run.id}`.toLowerCase().includes(needle)))
    .sort((a, b) => {
      const compared = filters.sort === "theorem" ? resultTitle(a).localeCompare(resultTitle(b))
        : (timeValue(a.lastWriteTs) - timeValue(b.lastWriteTs)) * (filters.sort === "oldest" ? 1 : -1);
      return compared || a.id.localeCompare(b.id);
    });
}

const RESULTS_KEY = "ensemble-prover.results-filters";

export function rememberedResultsFilters(): ResultsFilters {
  try { return normalizeResultsFilters(JSON.parse(sessionStorage.getItem(RESULTS_KEY) || "null")); }
  catch { return defaultResultsFilters(); }
}

export function rememberResultsFilters(filters: ResultsFilters): void {
  try { sessionStorage.setItem(RESULTS_KEY, JSON.stringify(filters)); }
  catch { /* Navigation in this page still retains the selected filters. */ }
}
