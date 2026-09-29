export type Polling = {
  refresh: () => Promise<void>;
  setPaused: (paused: boolean) => void;
  stop: () => void;
};

export function startPolling(load: (signal: AbortSignal) => Promise<void>, intervalMs: number, options: { paused?: boolean } = {}): Polling {
  let stopped = false;
  let paused = options.paused ?? false;
  let active: Promise<void> | null = null;
  let controller: AbortController | null = null;

  const refresh = (): Promise<void> => {
    if (stopped) return Promise.resolve();
    if (active) return active;
    controller = new AbortController();
    const current = Promise.resolve(load(controller.signal)).finally(() => {
      if (active === current) {
        active = null;
        controller = null;
      }
    });
    active = current;
    return current;
  };

  void refresh();
  const timer = window.setInterval(() => { if (!paused) void refresh(); }, intervalMs);
  return {
    refresh,
    setPaused(next: boolean) { paused = next; },
    stop() {
      if (stopped) return;
      stopped = true;
      window.clearInterval(timer);
      controller?.abort();
    },
  };
}
