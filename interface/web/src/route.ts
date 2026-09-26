import { resultsFromQuery, resultsToQuery } from "./results";
import type { ResultsFilters } from "./results";

export type Screen =
  | { name: "library"; filters?: ResultsFilters }
  | { name: "new" }
  | { name: "setup" }
  | { name: "progress" }
  | { name: "graph"; id?: string; follow?: boolean }
  | { name: "attempt"; id: string; follow?: boolean };

export function screenToHash(screen: Screen): string {
  if (screen.name === "library") {
    const query = screen.filters ? resultsToQuery(screen.filters) : "";
    return "#/library" + (query ? `?${query}` : "");
  }
  if (screen.name === "new") return "#/new";
  if (screen.name === "setup") return "#/setup";
  if (screen.name === "progress") return "#/";
  const query = screen.follow ? "?follow=sweep" : "";
  if (screen.name === "graph") return screen.id ? `#/graph/${encodeURIComponent(screen.id)}${query}` : "#/graph";
  return `#/attempt/${encodeURIComponent(screen.id)}${query}`;
}

export function hashToScreen(hash: string): Screen {
  const [raw, query = ""] = hash.replace(/^#/, "").split("?", 2);
  const follow = new URLSearchParams(query).get("follow") === "sweep";
  const path = raw.length === 0 ? "/" : raw.startsWith("/") ? raw : `/${raw}`;
  if (path === "/" || path === "/progress") return { name: "progress" };
  if (path === "/library") return { name: "library", filters: resultsFromQuery(query) };
  if (path === "/new") return { name: "new" };
  if (path === "/setup") return { name: "setup" };
  if (path === "/graph") return { name: "graph" };
  for (const name of ["attempt", "graph"] as const) {
    if (path.startsWith(`/${name}/`)) {
      try {
        const id = decodeURIComponent(path.slice(name.length + 2));
        if (id) return follow ? { name, id, follow: true } : { name, id };
      } catch { return { name: "library" }; }
    }
  }
  return { name: "library" };
}

export function screenKey(screen: Screen): string {
  return "id" in screen && screen.id ? `${screen.name}:${screen.id}` : screen.name;
}
