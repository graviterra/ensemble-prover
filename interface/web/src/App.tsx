import { useCallback, useEffect, useState } from "react";
import { Shell } from "./components/Shell";
import { hashToScreen, screenToHash } from "./route";
import type { Screen } from "./route";
import { defaultResultsFilters, rememberedResultsFilters, rememberResultsFilters } from "./results";
import type { ResultsFilters } from "./results";
import { WorkspaceScreen } from "./screens/WorkspaceScreen";
import { LibraryScreen } from "./screens/LibraryScreen";
import { NewWorkScreen } from "./screens/NewWorkScreen";
import { SetupScreen } from "./screens/SetupScreen";

export function App() {
  const [screen, setScreen] = useState<Screen>(() => hashToScreen(window.location.hash));
  const [libraryFilters, setLibraryFilters] = useState(rememberedResultsFilters);
  const [activeRunId, setActiveRunId] = useState<string>();
  const [activeFollow, setActiveFollow] = useState(false);
  const following = screen.name === "progress" || (screen.name === "graph" && !screen.id) || ("follow" in screen && screen.follow === true);
  useEffect(() => {
    if (screen.name === "library") {
      const filters = screen.filters ?? defaultResultsFilters();
      setLibraryFilters(filters);
      rememberResultsFilters(filters);
    }
  }, [screen]);
  useEffect(() => {
    if ("id" in screen && screen.id) setActiveRunId(screen.id);
    if (screen.name === "progress" || screen.name === "graph" || screen.name === "attempt") setActiveFollow(following);
  }, [screen, following]);
  useEffect(() => {
    const onChange = () => setScreen(hashToScreen(window.location.hash));
    window.addEventListener("hashchange", onChange);
    return () => window.removeEventListener("hashchange", onChange);
  }, []);
  const go = useCallback((next: Screen) => {
    if (next.name === "library" && !next.filters) next = { ...next, filters: libraryFilters };
    if ("id" in next && next.id) setActiveRunId(next.id);
    const hash = screenToHash(next);
    setScreen(next);
    if (window.location.hash !== hash) window.location.hash = hash;
  }, [libraryFilters]);
  const changeLibraryFilters = useCallback((filters: ResultsFilters) => {
    const next: Screen = { name: "library", filters };
    window.history.replaceState(window.history.state, "", screenToHash(next));
    setScreen(next);
  }, []);
  const runId = "id" in screen && screen.id ? screen.id : activeRunId;
  const chooseRun = useCallback((id: string) => {
    setActiveRunId(id);
    // Following replaces the displayed attempt in the current history entry.
    // It must update an explicit attempt URL as well as the remembered run.
    if (screen.name === "attempt" || screen.name === "graph" || screen.name === "progress") {
      const next: Screen = { name: screen.name === "graph" ? "graph" : "attempt", id, follow: following };
      window.history.replaceState(null, "", screenToHash(next));
      setScreen(next);
    }
  }, [screen.name, following]);
  return <Shell screen={screen} onNavigate={go} activeRunId={runId} activeFollow={activeFollow}>
    {screen.name === "library" ? <LibraryScreen filters={screen.filters ?? defaultResultsFilters()} onFiltersChange={changeLibraryFilters}
      onOpen={(id) => go({ name: "attempt", id })} onNew={() => go({ name: "new" })} /> : null}
    {screen.name === "new" ? <NewWorkScreen onOpen={(id) => go({ name: "attempt", id })} onLibrary={() => go({ name: "library" })} /> : null}
    {screen.name === "setup" ? <SetupScreen /> : null}
    {screen.name === "attempt" || screen.name === "progress" || screen.name === "graph" ?
      <WorkspaceScreen id={runId} expanded={screen.name === "graph"} followSweep={following} onChoose={chooseRun}
        onOpen={(id, follow = false) => go(screen.name === "graph" ? { name: "graph", id, follow } : { name: "attempt", id, follow })}
        onLibrary={() => go({ name: "library" })} onNew={() => go({ name: "new" })} /> : null}
  </Shell>;
}
