import { useEffect, useState } from "react";
import { catalogError, fetchCatalog } from "../catalog";
import type { Catalog } from "../catalog";

export function useCatalog() {
  const [catalog, setCatalog] = useState<Catalog | null>(null);
  const [error, setError] = useState("");
  const [loading, setLoading] = useState(true);
  const [revision, setRevision] = useState(0);
  useEffect(() => {
    const controller = new AbortController();
    setLoading(true);
    setError("");
    void fetchCatalog(controller.signal).then((value) => {
      if (!controller.signal.aborted) setCatalog(value);
    }).catch((cause: unknown) => {
      if (!controller.signal.aborted) setError(catalogError(cause));
    }).finally(() => {
      if (!controller.signal.aborted) setLoading(false);
    });
    return () => controller.abort();
  }, [revision]);
  return { catalog, error, loading, retry: () => setRevision((value) => value + 1) };
}
