import { useEffect, useId, useRef, useState } from "react";
import { createPortal } from "react-dom";
import { failureText, postStop } from "../api";
import { safeProse } from "../words";

export function StopDialog({
  runId,
  onDismiss,
  onDispatch,
  onRelease,
  onSignalled,
}: {
  runId: string;
  onDismiss: () => void;
  onDispatch: () => void;
  onRelease: () => void;
  onSignalled: () => void;
}) {
  const titleId = useId();
  const bodyId = useId();
  const dialogRef = useRef<HTMLDivElement>(null);
  const dismissRef = useRef<HTMLButtonElement>(null);
  const tokenRef = useRef("");
  const confirmOnce = useRef(false);
  const mounted = useRef(true);
  const [phase, setPhase] = useState<"preparing" | "ready" | "sending" | "error" | "unavailable">("preparing");
  const [message, setMessage] = useState("Preparing confirmation. Nothing has been sent yet.");

  useEffect(() => {
    mounted.current = true;
    const frame = document.getElementById("app-frame");
    frame?.setAttribute("inert", "");
    frame?.setAttribute("aria-hidden", "true");
    const previous = document.activeElement;
    dismissRef.current?.focus();
    return () => {
      mounted.current = false;
      frame?.removeAttribute("inert");
      frame?.removeAttribute("aria-hidden");
      if (previous instanceof HTMLElement) previous.focus();
    };
  }, []);

  useEffect(() => {
    const controller = new AbortController();
    let active = true;
    void (async () => {
      try {
        const result = await postStop(runId, null, controller.signal);
        if (!active) return;
        if (!result.confirmToken) {
          setPhase("unavailable");
          setMessage("The service did not offer a confirmation, so nothing was sent.");
          return;
        }
        tokenRef.current = result.confirmToken;
        setPhase("ready");
        setMessage("");
      } catch (error) {
        if (!active || (error instanceof DOMException && error.name === "AbortError")) return;
        setPhase("error");
        setMessage(failureText(error) || "The service could not prepare a confirmation. Nothing was sent.");
      }
    })();
    return () => {
      active = false;
      controller.abort();
    };
  }, [runId]);

  useEffect(() => {
    function onKey(event: KeyboardEvent) {
      if (event.key === "Escape") {
        event.preventDefault();
        event.stopPropagation();
        onDismiss();
        return;
      }
      if (event.key !== "Tab" || !dialogRef.current) return;
      const focusable = [...dialogRef.current.querySelectorAll<HTMLElement>("button:not([disabled])")];
      if (focusable.length === 0) return;
      const first = focusable[0];
      const last = focusable[focusable.length - 1];
      if (event.shiftKey && document.activeElement === first) {
        event.preventDefault();
        last.focus();
      } else if (!event.shiftKey && document.activeElement === last) {
        event.preventDefault();
        first.focus();
      }
    }
    document.addEventListener("keydown", onKey);
    return () => document.removeEventListener("keydown", onKey);
  }, [onDismiss]);

  async function confirm() {
    if (confirmOnce.current || phase !== "ready" || !tokenRef.current) return;
    confirmOnce.current = true;
    setPhase("sending");
    onDispatch();
    try {
      const result = await postStop(runId, tokenRef.current);
      if (result.signalled) {
        onSignalled();
        return;
      }
      onRelease();
      if (!mounted.current) return;
      confirmOnce.current = false;
      setPhase("error");
      setMessage(safeProse(result.detail) || "The service did not send an interrupt.");
    } catch (error) {
      onRelease();
      if (!mounted.current) return;
      confirmOnce.current = false;
      tokenRef.current = "";
      setPhase("preparing");
      setMessage(failureText(error) || "The service did not send an interrupt. Nothing was sent.");
      try {
        const refreshed = await postStop(runId, null);
        if (!mounted.current) return;
        if (!refreshed.confirmToken) {
          setPhase("unavailable");
          setMessage("The service did not offer a new confirmation, so nothing was sent.");
          return;
        }
        tokenRef.current = refreshed.confirmToken;
        setPhase("ready");
      } catch (refreshError) {
        if (!mounted.current) return;
        setPhase("error");
        setMessage(failureText(refreshError) || "The service could not prepare a new confirmation. Nothing was sent.");
      }
    }
  }

  const canSend = phase === "ready";

  return createPortal(
    <div
      className="backdrop"
      onMouseDown={(event) => {
        if (event.target === event.currentTarget) onDismiss();
      }}
    >
      <div
        className="dialog"
        role="dialog"
        aria-modal="true"
        aria-labelledby={titleId}
        aria-describedby={bodyId}
        ref={dialogRef}
        tabIndex={-1}
      >
        <h2 id={titleId}>Stop this attempt?</h2>
        <div id={bodyId}>
          <p>One cooperative interrupt is sent. A second click must not send another. Closing this page does not stop a run.</p>
          <p>Escape closes this dialog and does not send an interrupt.</p>
          {message ? <p role="status">{message}</p> : null}
        </div>
        <div className="dialog-actions">
          <button ref={dismissRef} type="button" className="button" onClick={onDismiss}>
            Keep working
          </button>
          <button type="button" className="button button-primary" onClick={() => void confirm()} disabled={!canSend}>
            {phase === "sending" ? "Sending…" : "Send one interrupt"}
          </button>
        </div>
      </div>
    </div>,
    document.body,
  );
}
