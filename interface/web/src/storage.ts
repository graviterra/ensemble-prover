import type { StartKind } from "./types";

const SETUP_KEY = "ensemble-prover.setup";
const DRAFT_KEY = "ensemble-prover.draft";
const STOP_KEY = "ensemble-prover.stop-sent";
const START_SUBMISSIONS_KEY = "ensemble-prover.start-submissions";

export type Setup = {
  projectPath: string;
  prover: string;
  proverModel: string;
};

export type LeanDraft = {
  projectPath: string;
  leanFile: string;
  theorem: string;
  prover: string;
  proverModel: string;
};

export type EnglishDraft = {
  projectPath: string;
  text: string;
  prover: string;
  proverModel: string;
  formalizeOnly: boolean;
};

export type NotesDraft = {
  projectPath: string;
  sourceFiles: string[];
  goal: string;
};

export type QuestionDraft = {
  projectPath: string;
  text: string;
};

export type Drafts = {
  start: StartKind | null;
  lean: LeanDraft;
  english: EnglishDraft;
  notes: NotesDraft;
  question: QuestionDraft;
};

type PendingStart = {
  fingerprint: string;
  idempotencyKey: string;
};

type PendingStarts = Partial<Record<StartKind, PendingStart[]>>;

export class StartIdentityStorageError extends Error {
  constructor() {
    super("This browser cannot safely retry this start because its retry identity could not be saved. No work was started.");
    this.name = "StartIdentityStorageError";
  }
}

export const emptySetup: Setup = { projectPath: "", prover: "", proverModel: "" };

function readObject(key: string): Record<string, unknown> | null {
  try {
    const raw = localStorage.getItem(key);
    if (!raw) return null;
    const parsed = JSON.parse(raw) as unknown;
    if (!parsed || typeof parsed !== "object" || Array.isArray(parsed)) return null;
    return parsed as Record<string, unknown>;
  } catch {
    return null;
  }
}

function text(value: unknown): string {
  return typeof value === "string" ? value : "";
}

export function loadSetup(): Setup {
  const row = readObject(SETUP_KEY);
  if (!row) return { ...emptySetup };
  return {
    projectPath: text(row.projectPath),
    prover: text(row.prover),
    proverModel: text(row.proverModel),
  };
}

export function saveSetup(setup: Setup): void {
  localStorage.setItem(
    SETUP_KEY,
    JSON.stringify({
      projectPath: setup.projectPath,
      prover: setup.prover,
      proverModel: setup.proverModel,
    }),
  );
}

function blankDrafts(setup: Setup): Drafts {
  return {
    start: null,
    lean: { projectPath: setup.projectPath, leanFile: "", theorem: "", prover: setup.prover, proverModel: setup.proverModel },
    english: { projectPath: setup.projectPath, text: "", prover: setup.prover, proverModel: setup.proverModel, formalizeOnly: false },
    notes: { projectPath: setup.projectPath, sourceFiles: [""], goal: "" },
    question: { projectPath: "", text: "" },
  };
}

function fill(value: string, fallback: string): string {
  return value.trim() ? value : fallback;
}

function draftModel(row: Record<string, unknown>, setup: Setup): string {
  // An empty model on a chosen provider means its CLI default was selected.
  if (text(row.prover).trim()) {
    if (typeof row.proverModel === "string") return row.proverModel;
    return row.prover === setup.prover ? setup.proverModel : "";
  }
  return fill(text(row.proverModel), setup.proverModel);
}

export function loadDrafts(setup: Setup): Drafts {
  const base = blankDrafts(setup);
  const row = readObject(DRAFT_KEY);
  if (!row) return base;
  const lean = row.lean && typeof row.lean === "object" ? (row.lean as Record<string, unknown>) : {};
  const english = row.english && typeof row.english === "object" ? (row.english as Record<string, unknown>) : {};
  const notes = row.notes && typeof row.notes === "object" ? (row.notes as Record<string, unknown>) : {};
  const question = row.question && typeof row.question === "object" ? (row.question as Record<string, unknown>) : {};
  const sourceFiles = Array.isArray(notes.sourceFiles)
    ? notes.sourceFiles.filter((item): item is string => typeof item === "string")
    : [];
  const start = row.start === "lean" || row.start === "english" || row.start === "notes" || row.start === "question" ? row.start : null;
  return {
    start,
    lean: {
      projectPath: fill(text(lean.projectPath), setup.projectPath),
      leanFile: text(lean.leanFile),
      theorem: text(lean.theorem),
      prover: fill(text(lean.prover), setup.prover),
      proverModel: draftModel(lean, setup),
    },
    english: {
      projectPath: fill(text(english.projectPath), setup.projectPath),
      text: text(english.text),
      prover: fill(text(english.prover), setup.prover),
      proverModel: draftModel(english, setup),
      formalizeOnly: english.formalizeOnly === true,
    },
    notes: {
      projectPath: fill(text(notes.projectPath), setup.projectPath),
      sourceFiles: sourceFiles.length > 0 ? sourceFiles : [""],
      goal: text(notes.goal),
    },
    question: {
      projectPath: text(question.projectPath),
      text: text(question.text),
    },
  };
}

export function saveDrafts(drafts: Drafts): void {
  localStorage.setItem(DRAFT_KEY, JSON.stringify(drafts));
}

function stableValue(value: unknown): unknown {
  if (Array.isArray(value)) return value.map(stableValue);
  if (!value || typeof value !== "object") return value;
  return Object.fromEntries(
    Object.entries(value as Record<string, unknown>)
      .filter(([key]) => key !== "idempotencyKey")
      .sort(([left], [right]) => left.localeCompare(right))
      .map(([key, child]) => [key, stableValue(child)]),
  );
}

function readPendingStarts(storage: Storage): PendingStarts {
  let row: Record<string, unknown> | null = null;
  try {
    const raw = storage.getItem(START_SUBMISSIONS_KEY);
    if (raw) {
      const parsed = JSON.parse(raw) as unknown;
      if (parsed && typeof parsed === "object" && !Array.isArray(parsed)) {
        row = parsed as Record<string, unknown>;
      }
    }
  } catch {
    throw new StartIdentityStorageError();
  }
  if (!row) return {};
  const result: PendingStarts = {};
  for (const kind of ["lean", "english", "notes", "question"] as const) {
    const candidate = row[kind];
    const records = Array.isArray(candidate) ? candidate : [candidate];
    result[kind] = records.flatMap((item: unknown) => {
      if (!item || typeof item !== "object" || Array.isArray(item)) return [];
      const record = item as Record<string, unknown>;
      if (typeof record.fingerprint !== "string" || typeof record.idempotencyKey !== "string") return [];
      if (!record.fingerprint || !record.idempotencyKey) return [];
      return [{ fingerprint: record.fingerprint, idempotencyKey: record.idempotencyKey }];
    });
  }
  return result;
}

function writePendingStarts(storage: Storage, starts: PendingStarts): void {
  try {
    storage.setItem(START_SUBMISSIONS_KEY, JSON.stringify(starts));
  } catch {
    throw new StartIdentityStorageError();
  }
}

function startStorage(storage?: Storage): Storage {
  if (storage) return storage;
  try {
    return sessionStorage;
  } catch {
    throw new StartIdentityStorageError();
  }
}

function newIdempotencyKey(): string {
  if (typeof crypto.randomUUID === "function") return crypto.randomUUID();
  const bytes = new Uint8Array(16);
  crypto.getRandomValues(bytes);
  return [...bytes].map((byte) => byte.toString(16).padStart(2, "0")).join("");
}

export function prepareStartSubmission<T extends Record<string, unknown>>(
  kind: StartKind,
  payload: T,
  storage?: Storage,
): { idempotencyKey: string; payload: T & { idempotencyKey: string } } {
  const target = startStorage(storage);
  const fingerprint = JSON.stringify(stableValue(payload));
  const starts = readPendingStarts(target);
  const pending = starts[kind] ?? [];
  const current = pending.find((item) => item.fingerprint === fingerprint);
  const idempotencyKey = current?.idempotencyKey ?? newIdempotencyKey();
  if (!current) pending.push({ fingerprint, idempotencyKey });
  starts[kind] = pending;
  writePendingStarts(target, starts);
  return { idempotencyKey, payload: { ...payload, idempotencyKey } };
}

export function completeStartSubmission(
  kind: StartKind,
  idempotencyKey: string,
  storage?: Storage,
): void {
  try {
    const target = startStorage(storage);
    const starts = readPendingStarts(target);
    const pending = starts[kind];
    if (!pending?.some((item) => item.idempotencyKey === idempotencyKey)) return;
    starts[kind] = pending.filter((item) => item.idempotencyKey !== idempotencyKey);
    if (starts[kind]?.length === 0) delete starts[kind];
    writePendingStarts(target, starts);
  } catch {
    // Keeping a completed key is safe: a later retry remains idempotent.
  }
}

export function wasStopSent(id: string): boolean {
  try {
    const raw = sessionStorage.getItem(STOP_KEY);
    const list = raw ? (JSON.parse(raw) as unknown) : [];
    return Array.isArray(list) && list.includes(id);
  } catch {
    return false;
  }
}

export function markStopSent(id: string): void {
  const current = (() => {
    try {
      const raw = sessionStorage.getItem(STOP_KEY);
      const list = raw ? (JSON.parse(raw) as unknown) : [];
      return Array.isArray(list) ? list.filter((item): item is string => typeof item === "string") : [];
    } catch {
      return [];
    }
  })();
  try {
    sessionStorage.setItem(STOP_KEY, JSON.stringify([...new Set([...current, id])]));
  } catch {
    // A storage failure does not undo the service's confirmed interrupt.
  }
}
