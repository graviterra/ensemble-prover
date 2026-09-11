# Autonomous mathematical research — experimental

Last updated: 2026-09-10.

This executable loop investigates a mathematical problem, starts alternative
research programs, shares complete arguments, commissions fresh reviews, and
optionally runs isolated Python experiments. It may pursue a proof, counterexample,
construction, representation, intermediate conjecture, or precise gap. Alternative
approaches do not become extra hypotheses of the original target.
With a built Lake project, one `discovery run` also drives formalization,
independent statement review, Mini proof search, checked export, and feedback
to the investigator. Without a project, research remains standalone.

## Start and inspect a run

Use the repository's Python environment and a complete UTF-8 problem file.
Initialization is offline and preserves the original text. The default transport
is the OpenAI API. Choose model names available to your selected provider.

```bash
python -m ensemble_prover.research_claims discovery init runs/research/example \
  --problem problem.txt \
  --project-path /path/to/built-lake-project \
  --model gpt-5.6-sol --review-model gpt-6-astra \
  --max-requests 32 --max-seconds 3600 --concurrency 4

python -m ensemble_prover.research_claims discovery status runs/research/example
```

Supply additional complete documents with repeated `--source FILE` options.
The project must already exist and be built. Use repeated `--import MODULE`
options for trusted project imports; these require `--project-path`. Omit the
project for research-only execution without automatic formalization.
The Python `initialize` API also accepts a structured `ClaimSpec` with separate
hypotheses and quantifiers. Source content is mathematical data, not permission
to execute instructions.

With the default provider, the following command **spends API credits** using
`OPENAI_API_KEY` and the saved model names through the existing provider routing:

```bash
python -m ensemble_prover.research_claims discovery run runs/research/example
```

To use your Codex ChatGPT subscription instead, run `codex login` and add
`--provider codex` at initialization, with Codex model names. Reviewers inherit
that provider unless you explicitly set `--review-provider openai`; the reverse
mixed configuration is also supported. Codex-only research needs no API key
and never falls back to API billing. `--codex-bin` selects a saved CLI executable.
The saved `--provider`/`--model` select research, formalizer, Mini prover, and
refiner roles. `--review-provider`/`--review-model` select both argument and
semantic statement reviewers. No additional model flags or run commands are
needed for the integrated loop. The standalone NL and formalization CLIs remain
API-backed; discovery injects its clients into the formalization core. Claude
Code is supported by Mini only.
See [subscription setup](../../docs/CODEX_SUBSCRIPTION_BACKEND.md#autonomous-research).

Progress events go to stderr; final structured status goes to stdout. Inspect
complete arguments and reviews with the ledger commands:

```bash
python -m ensemble_prover.research_claims history runs/research/example root
python -m ensemble_prover.research_claims read-artifact runs/research/example SHA256 \
  --output complete-artifact.txt
```

## Automatic formalization, proof, and feedback

When the project is configured, a written proof with a `supported` review or a
counterexample with a `refuted` review automatically queues a formalization
campaign. A worker may also emit `formalize` with its complete `proof_plan`.
Optional `"polarity": "refute"` asks for a formal proof of the original claim's
logical negation, retaining its domain, hypotheses, and quantifier scope.
Neither an argument nor a review vote confers proof authority.

Each campaign receives the exact claim revision, original target and documents,
complete original proof plan, and a frozen snapshot of shared research artifacts.
The original plan remains required downstream context, including during Mini
proof work. Changed shared claims reject stale work. The campaign independently
reviews the proposed formal statement before proof acceptance.

| Initialization option | Default | Effect |
| --- | --- | --- |
| `--proof-quantum-s` | 600 seconds | Bounds a proof interval before feedback returns to research, within the overall deadline. |
| `--formalization-steps` | 8 | Maximum campaign controller steps per proof interval. |
| `--lean-timeout-s` | 300 seconds | Lean operation timeout. |

The investigator receives results or failure feedback with complete task state
and artifact references for full diagnostics. It can emit
`continue_formalization` with the assigned `program_id` to resume its paused
campaign. That preserves the reviewed target, completed modules, and saved work.
A changed plan or response to `needs_clarification` requires a new `formalize`
action with the complete revised plan; it creates a fresh campaign and independent
statement review. Prior attempts and diagnostics remain available.

Campaigns live under `DIRECTORY/campaigns/JOB_ID/`. Successful exports use unique
`verified-…` subdirectories and record hashes in a receipt. Discovery accepts a
result only after the export is independently checked and bound to the exact
claim revision, polarity, frozen reviewed statement, and saved environment.
`discovery status` revalidates receipts and artifacts and lists them under
`verified_proofs`. Only a checked root proof sets `root_proved`; only a checked
proof of the root's negation sets `root_refuted`. A verified helper sets neither.
Modified export files or invalid receipts fail validation. A normal claim revision
withdraws affected receipt authority and lists it under `stale_proofs`, while status
remains readable and historical artifacts remain available. Resume retires stale
proof jobs without new budget; changing the original target still stops the run.

Natural-language alignment remains `machine_reviewed_not_certified`. Lean checks
the formal statement; the correspondence to the prose is independently model
reviewed, not mathematically certified. The manual ledger's `kernel_report`
records and `assessment.verification.kernel_verified` do not acquire authority
from this path; verified discovery exports are reported separately.

## Budget and recovery contract

- `--max-requests` counts durable **dispatch intents**, including retries,
  compatibility fallbacks, research, argument and semantic reviews, formalization,
  nested Mini prover/refiner dispatches, and resumed requests. An API dispatch is one
  HTTP request; a Codex dispatch is one `codex exec` invocation. The CLI's internal
  HTTP reconnects are not individually observable. It is not a dollar or
  token cap; one long response can still be expensive.
- Reservations commit before provider exposure. Interrupted and rejected requests
  are not automatically refunded, even when the provider charged nothing.
- The wall-clock limit begins at first execution and includes downtime. Repeating
  `discovery run` resumes within the original limits; it does not reset them.
- Ctrl-C preserves state. After restoring account/transport access, repeat the run
  command to explicitly resume. An interrupted request with an unknown outcome may
  be issued again using another reservation; exactly-once provider execution is
  not promised.
- Saved responses are applied without another paid request, including after budget
  exhaustion. Mathematical mutations and response consumption commit together.
- Formalization campaigns retain reviewed contracts, completed modules, and pending
  source across interruption. An interrupted inner Mini invocation may restart
  under the same global budget. Bounded local finalization can recover a saved
  proof after provider authorization ends, without issuing another model request;
  after the deadline, this recovery is bounded by the saved Lean timeout.
- One controller process owns the run. Workers operate asynchronously up to the
  configured concurrency. Reviews have priority, then formalization; research
  turns use a durable FIFO queue, with new programs and continuing turns joining its tail. Repeated
  delegation cannot continually jump ahead of older waiting research turns.
  This is single-host, not a distributed fleet runtime.
- Provider failures are operational pauses, not mathematical verdicts. Changing
  the original target stops execution instead of silently changing the problem.
  Changing a child claim retires that child's stale invocation and notifies its
  unchanged parent, which can choose another route within the existing budget.

There is no automatic budget extension. Exhausted runs remain inspectable;
additional model work requires a newly authorized discovery run or separately
authorized standalone campaign.

New ledgers use schema 6, with explicit closed-loop authorization. Stop older
clients, back up version 1–5 ledgers, and explicitly upgrade them:

```bash
python -m ensemble_prover.research_claims upgrade DIRECTORY
```

Upgrading preserves records, budgets, and existing providers. Older API-only runs
receive explicit API routing metadata. Existing runs remain research-only;
upgrading does not authorize automatic proving. Initialize a new directory with
`--project-path` for that workflow. Missing routing or closed-loop authorization
fields in new-format runs fail closed.

## Reviews and full content

Investigators cannot issue kernel certificates or review their own submissions.
Reviews use fresh conversations and runtime-assigned identities. This is procedural
separation, not a guarantee that models make independent mistakes.

Feedback arriving during a request stays in a durable inbox. A stale finish
response cannot ignore an unseen adverse review or child result. A program can
`wait` for its pending child investigations or reviews without spending model
calls. A child conclusion or independently reviewed child argument wakes its
parent, even if the parent had finished. The full result is delivered, and any
further requests still use the original budget. Changing the parent's claim
prevents a stale continuation from reopening it. Explicit re-review can retire a
filled gap or supersede named earlier assessments; unlisted dissent remains active.

Original documents, requests, raw responses, full arguments, experiment results,
and proof plans are retained as hashed artifacts. Reviewers receive complete
assigned arguments. Other arguments have exact artifact IDs and can be retrieved
in full. Required conversation content is not silently truncated. A context-window
overflow is explicit; automatic context compaction is not implemented here.
The Codex adapter preserves the complete serialized request, but Codex may
manage or compact its own context internally. Exact underlying-model delivery
cannot be attested by the host. Subscription failures expose only classified
backend/kind fields in status, not raw authentication diagnostics.
The first run-stopping error remains the primary diagnostic; each failed job
also retains its own structured `last_error_details`. A completed Codex answer
with malformed action text is saved before the discovery parser supplies
correction feedback. Invalid outer envelopes, native action events, and
incomplete turns still fail at the transport boundary and cannot install proof
evidence.

`supported` means a recorded written argument passed review, not that Lean accepted
it. In research-only mode, discovery `root_proved` and `root_refuted` remain false.
Neither finite computations nor local novelty establish an infinite theorem or
literature priority.

## Optional computation

Add `--experiments` at initialization to enable Python standard-library experiments.
They require an unprivileged Linux process, `/usr/bin/bwrap` with user-namespace support, and
`/usr/bin/python3`. Missing isolation produces `tool_unavailable`; there is no
unsandboxed fallback.

Experiments have no host home/project mounts, inherited credentials, network,
writable scratch filesystem, or subprocess permission. The system runtime is
read-only. Defaults are 20 seconds, a 512 MiB per-process address-space limit,
and 1,000,000 captured output bytes. These are resource limits, not a cgroup
memory guarantee. Packages cannot be installed. Use an unprivileged dedicated
environment for hostile workloads and keep the operating system updated.

Excess output stops computation and is explicitly marked incomplete. Interrupted
experiments have an unknown outcome and are not automatically repeated. Neither
case is admitted as a successful mathematical observation.

Results retain exact captured bytes in `stdout_base64` and `stderr_base64`, with
separate byte counts. The `stdout` and `stderr` text fields are display views;
`stdout_text_lossy` or `stderr_text_lossy` marks invalid UTF-8. The combined output
quota applies to raw captured bytes, not the larger JSON/base64 representation.
An incomplete result retains only the captured prefix and says so explicitly.

## Exact handoff to the existing formalizer

For research-only runs, a worker's `formalize` action saves a complete,
revision-bound handoff. Its artifact ID appears in status under `handoffs`.
Initialize standalone formalization without model calls:

```bash
python -m ensemble_prover.research_claims discovery formalize runs/research/example SHA256 \
  --project-path path/to/lean_project --output runs/formalization/example
```

The formalizer receives the exact contract, original documents, complete proof
plan, and a frozen ledger snapshot with every artifact present when the handoff
was saved. This includes arguments from child, sibling, and deeper investigations;
later additions are excluded. UTF-8 artifacts retain their exact text, and binary
artifacts use explicit base64 envelopes with an artifact index. A revised shared
claim rejects a stale handoff. Older incomplete handoff formats are rejected;
save a fresh handoff rather than silently omitting their supporting arguments.
Formalization still requires its own statement review and Lean admission.

Running that campaign through `python -m ensemble_prover.formalization run ...`
is a separate authorization. Its nested prover requests are **not** covered by
the research request cap. This separate campaign uses the standalone CLI's API
model settings. Automatic proof work inside `discovery run` uses the saved
discovery providers and shares its global cap instead.

Other current limits: no automatic literature search, learned portfolio allocator,
cross-run method library, distributed execution, or empirical discovery-performance
claim. Three offline scripted/fake-Codex trajectories exercise real Lean
verification and feedback; these are integration tests, not discovery-performance
benchmarks. Optional computation has separate isolation tests. Paid model
benchmarks require separate authorization.
