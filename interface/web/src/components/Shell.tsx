import { useEffect, useRef } from "react";
import type { ReactNode } from "react";
import type { Screen } from "../route";
import { screenKey } from "../route";

export function Shell({ screen, onNavigate, activeRunId, activeFollow = false, children }: {
  screen: Screen; onNavigate: (screen: Screen) => void; activeRunId?: string; activeFollow?: boolean; children: ReactNode;
}) {
  const mainRef = useRef<HTMLElement>(null);
  const skipFirst = useRef(true);
  const current = screen.name === "attempt" ? "progress" : screen.name;
  const navigationKey = screenKey(screen);
  const progressScreen: Screen = activeRunId ? { name: "attempt", id: activeRunId, follow: activeFollow } : { name: "progress" };
  const items: { label: string; screen: Screen; name: string }[] = [
    { label: "Launcher", screen: { name: "new" }, name: "new" },
    { label: "Progress", screen: progressScreen, name: "progress" },
    { label: "Graph & evidence", screen: { name: "graph", id: activeRunId, follow: activeFollow }, name: "graph" },
    { label: "Results", screen: { name: "library" }, name: "library" },
    { label: "Setup", screen: { name: "setup" }, name: "setup" },
  ];
  useEffect(() => {
    const titles = { library: "Results", new: "Launcher", setup: "Setup", attempt: "Progress", progress: "Progress", graph: "Graph & evidence" };
    document.title = `${titles[screen.name]} · Ensemble Prover`;
    if (skipFirst.current) { skipFirst.current = false; return; }
    mainRef.current?.focus();
  }, [screen.name, navigationKey]);
  return <div className="frame" id="app-frame">
    <a className="skip" href="#content" onClick={(event) => { event.preventDefault(); mainRef.current?.focus(); mainRef.current?.scrollIntoView(); }}>Skip to content</a>
    <header className="topbar">
      <button type="button" className="brand" onClick={() => onNavigate(progressScreen)}>Ensemble Prover</button>
      <nav className="topbar-nav" aria-label="Sections">{items.map((item) => <button key={item.name} type="button"
        className="nav-button" aria-current={current === item.name ? "page" : undefined} onClick={() => onNavigate(item.screen)}>{item.label}</button>)}</nav>
    </header>
    <main id="content" className="main" tabIndex={-1} ref={mainRef} data-screen={screenKey(screen)}><div className="main-inner">{children}</div></main>
  </div>;
}
