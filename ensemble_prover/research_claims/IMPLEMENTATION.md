# Research claim ledger: initial implementation

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
handoffs. It does not infer equivalence of mathematical prose or issue Lean
certificates. Existing prover and campaign acceptance remain unchanged. See
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
  and child-result notifications that wake waiting or finished parents.
- `experiments.py`: optional fail-closed namespace-isolated Python observations.

Correctness is `proposed`, `supported`, `refuted`, or `unresolved`. Verification
lists written arguments, independent reviews, finite computations, source
checks, and reported kernel artifacts separately. A reported kernel artifact
remains historical, unverified metadata in this ledger.

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
wait/child-result continuation semantics. Record-preserving upgrades from
versions 1, 2, and 3 require operator action; budgets are not reset.

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

## Follow-on work

Fresh verification adapters for Mini/campaign artifacts, shared execution budgets
across formalization and research, and automatic source lookup are later stages.
They must bind exact claim revisions and environments before obtaining any
formal authority. The initial ledger records human/agent assertions and their
provenance; independent reviewer identity is asserted locally, not authenticated.
