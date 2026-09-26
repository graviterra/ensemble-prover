export type LibraryRun = {
  id: string;
  label: string;
  kind: string;
  problem: string;
  exportState: string;
  internalSolved: boolean;
  rootStatus: string;
  hasSummary: boolean;
  lastWriteTs: number | string | null;
  launchId: string;
  launchStatus: string;
  formalizationStatus: string;
};

export type Lane = {
  name: string;
  count: number;
  lastText: string;
  lastElapsedS?: number | null;
};

export type Milestone = {
  elapsedS: number;
  text: string;
  kind: string;
};

export type GraphNode = {
  id: string;
  label: string;
  status: string;
  kind?: "root" | "helper";
  supports?: string[];
  recordedAtS?: number | null;
};

export type RunDetail = {
  kind: string;
  problem: string;
  exportState: string;
  exportReason: string;
  internalSolved: boolean;
  rootStatus: string;
  childRootFinalizations: number | null;
  lastEventS?: number | null;
  process: { status: string; detail: string };
  lanes: Lane[];
  milestones: Milestone[];
  events?: (Milestone & { scope: string })[];
  graph: GraphNode[];
  nodeEvidence?: Record<string, NodeEvidence>;
  helpers: unknown;
  costFields: Record<string, unknown>;
  launchId: string;
  launchStatus: string;
  formalization: Formalization;
};

export type NodeEvidence = {
  statement: string;
  leanSource: string;
  scope: string;
  source: string;
  reason: string;
};

export type Formalization = {
  status: string;
  statement: string;
  message: string;
  leanSource: string;
  leanFile: string;
  artifactFiles: string[];
};

export type StopResult = {
  signalled: boolean;
  confirmToken: string;
  detail: string;
};

export type StartKind = "lean" | "english" | "notes" | "question";
