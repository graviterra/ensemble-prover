# Research claim ledger and discovery implementation

Last updated: 2026-09-10.

The maintained prover runs through `mini_prover` → `mini_session.factory` →
`MiniSession`. `ProofDossier`, `ProofGraph`, and `ProofState` record formal search;
Lean checks and root finalization govern proof acceptance. The existing
`formalization` campaign supplies source-grounded task decomposition, semantic
review, and compiler admission. None of these statuses means that a written
research result makes a useful quantitative contribution to a conjecture.

This implementation uses a separate, local research ledger for a coordinated
mathematical research workflow. It implements the bookkeeping and bounded
assignment layer plus an experimental autonomous execution layer. The latter
dispatches model investigations and reviews with durable request admission,
executes optional isolated Python experiments, and saves exact formalization
handoffs. A built project configured at `discovery init --project-path` enables
automatic formalization, Mini proof search, independently checked export, and
feedback within the same `discovery run`. Existing prover and campaign acceptance
gates remain in force. Natural-language alignment is model reviewed, not certified.
See
[DISCOVERY.md](DISCOVERY.md) for the execution contract and current limits.

## Components

- `model.py`: exact mathematical contracts, quantitative costs, dependency
  obligations, claim specifications, input validation.
- `store.py`: versioned SQLite ledger; immutable revisions and artifacts;
  revision-fenced evidence, independent reviews, contribution decisions,
  operations, assignments and events.
- `scheduler.py`: explainable remaining-obligation priorities and complete,
  bounded complementary assignment packets.
- `cli.py`, `__main__.py`: JSON submissions, reports, exports and module entry.
- `discovery.py`, `discovery_store.py`, `discovery_cli.py`: executable research
  programs, independent reviews, shared admission, durable response recovery,
  proof scheduling, and child/proof-result notifications that wake waiting or
  finished parents.
- `proof_bridge.py`: revision- and environment-bound formalization campaigns,
  exact required downstream context, injected model clients, Mini execution,
  full feedback, independently checked exports, and validated receipts.
- `experiments.py`: optional fail-closed namespace-isolated Python observations.

Correctness is `proposed`, `supported`, `refuted`, or `unresolved`. Verification
lists written arguments, independent reviews, finite computations, source
checks, and reported kernel artifacts separately. A reported kernel artifact
remains historical, unverified metadata in this ledger. Discovery separately
reports `verified_proofs`, `root_proved`, and `root_refuted`; only a freshly checked
export can produce a receipt. Status revalidates the receipt's frozen reviewed
target, exact claim revision and polarity, saved environment, and file hashes.
Claim revisions withdraw affected receipts from current authority and expose
`stale_proofs` without preventing status inspection. Resume retires stale proof
jobs under the original authorization, preserving historical artifacts.
Refutation requires proving the original proposition's logical negation.
Natural-language alignment remains `machine_reviewed_not_certified`.

With a project configured, reviewed proofs/counterexamples automatically queue
formalization. A `formalize` action can also provide a complete plan with optional
`polarity: refute`. `continue_formalization` resumes the same paused campaign;
a changed plan or clarification starts a fresh campaign and statement review.
The original source, claim, and complete plan remain required downstream context,
and all diagnostic artifacts are retained for feedback.

Research, formalizer, prover, and refiner inherit the saved `provider`/`model`;
argument and semantic reviewers inherit `review_provider`/`review_model`.
The integrated loop supports OpenAI API and Codex subscription clients. Standalone
NL/formalization CLIs remain API-backed, and Claude Code remains Mini-only.
An additive transport dispatch guard charges every nested concrete dispatch to
the discovery ledger without replacing Mini's own observer. Request limits span
roles and resumes; the wall-clock limit includes downtime. Default proof intervals
are 600 seconds and 8 campaign controller steps, with a 300-second Lean timeout.
Saved campaigns retain reviewed contracts, completed modules, and pending source;
an interrupted inner Mini invocation may restart within the same global budget.
Bounded local finalization can recover an already saved proof after provider
authorization ends without allowing a new model request.

Each parent dependency declares its own required contract and quantitative
requirements. Supported helpers do not automatically close those obligations.
Closure requires compatible exact statement/domain/quantifier text, no extra
hypotheses, an independent contribution review, and explicit acceptance of
quantitative costs. Unknown costs cannot close a quantitative requirement.
Refutation eliminates a proposed route; it never proves its parent.

Review records are append-only. Explicit supersession can resolve a mistaken
assessment, while unlisted conflicting reviews remain active. Dismissing invalid
evidence never creates proof authority. Contribution consensus is separate from
the individual reviewers' preserved rationales. Schema version 4 retains the
version 2 review semantics and version 3 runtime tables, adding explicit
wait/child-result continuation semantics. Version 5 adds a provider-routing
compatibility fence: older clients cannot misroute subscription discovery runs
through the API. Version 6 adds explicit closed-loop authorization. Record-preserving
upgrades from versions 1–5 require operator action and retain providers and budgets.
They leave automatic proving disabled; a new run with a configured project is
required to authorize it.

Changing a claim increments its revision and invalidates dependent claims and
their assessments transitively. Old evidence, reviews, failed routes and
operational outcomes remain available in history. Concurrent submissions carry
expected revisions and reject stale work. Each connection uses a transaction
for mutations and a consistent read snapshot for reports. Assignments fence
history and assessment tokens as well as revisions, including new evidence that
arrives without a statement change.

## Validation targets

- Reopen a ledger without losing exact source bytes, evidence or review history.
- Reject malformed input, cycles, missing dependencies and stale publications.
- Reject author self-review and counterexamples without hypothesis/violation
  descriptions; finite computations alone do not establish general claims.
- Keep a correct but irrelevant helper out of contribution progress.
- Detect statement, domain, hypothesis, quantifier and quantitative mismatches.
- Invalidate descendants on revision; preserve old failed-route evidence.
- Keep timeouts, provider errors and unavailable tools out of mathematical
  assessments.
- Generate bounded assignments with exact context, prior failures, an owned
  output, quantitative checks and permission to report a gap or counterexample.
- Exercise the CLI lifecycle without providers or Lean, then run affected
  existing tests to confirm package isolation.
- Exercise research → formalization → Mini → independently checked export →
  feedback against real Lean with scripted/fake-Codex responses. Three tested
  trajectories validate integration; they do not measure discovery performance.
- Reject stale bindings, modified exports, missing receipts, and manual kernel
  reports as proof authority; enforce shared admission at nested dispatches.

## Follow-on work

Automatic literature/source lookup, learned portfolio allocation, a cross-run
method library, and distributed execution remain unimplemented. Discovery
performance and literature novelty have not been established. Research-only runs
remain available without a project; manually launched formalization campaigns
keep separate authorization and budgets. The manual ledger records human/agent
assertions and provenance; reviewer identity there is asserted locally, not
authenticated.
