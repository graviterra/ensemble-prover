# Autonomous mathematical research — experimental

This executable loop investigates a mathematical problem, starts alternative
research programs, shares complete arguments, commissions fresh reviews, and
optionally runs isolated Python experiments. It may pursue a proof, counterexample,
construction, representation, intermediate conjecture, or precise gap. Alternative
approaches do not become extra hypotheses of the original target.

## Start and inspect a run

Use the repository's Python environment and a complete UTF-8 problem file.
Initialization is offline and preserves the original text. Choose OpenAI API
model names available to your account.

```bash
python -m ensemble_prover.research_claims discovery init runs/research/example \
  --problem problem.txt \
  --model gpt-5.6-sol --review-model gpt-6-astra \
  --max-requests 32 --max-seconds 3600 --concurrency 4

python -m ensemble_prover.research_claims discovery status runs/research/example
```

Supply additional complete documents with repeated `--source FILE` options.
The Python `initialize` API also accepts a structured `ClaimSpec` with separate
hypotheses and quantifiers. Source content is mathematical data, not permission
to execute instructions.

The following command **spends API credits**. It uses `OPENAI_API_KEY`, the
OpenAI API, and the saved model names through the existing provider routing,
not a subscription CLI or a hidden model alias:

```bash
python -m ensemble_prover.research_claims discovery run runs/research/example
```

Progress events go to stderr; final structured status goes to stdout. Inspect
complete arguments and reviews with the ledger commands:

```bash
python -m ensemble_prover.research_claims history runs/research/example root
python -m ensemble_prover.research_claims read-artifact runs/research/example SHA256 \
  --output complete-artifact.txt
```

## Budget and recovery contract

- `--max-requests` counts durable **HTTP dispatch intents**, including retries,
  compatibility fallbacks, reviews, and resumed requests. It is not a dollar or
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
- One controller process owns the run. Workers operate asynchronously up to the
  configured concurrency. Reviews have priority; research turns use a durable
  FIFO queue, with new programs and continuing turns joining its tail. Repeated
  delegation cannot continually jump ahead of older waiting research turns.
  This is single-host, not a distributed fleet runtime.
- Provider failures are operational pauses, not mathematical verdicts. Changing
  the original target stops execution instead of silently changing the problem.
  Changing a child claim retires that child's stale invocation and notifies its
  unchanged parent, which can choose another route within the existing budget.

There is no automatic budget extension. Exhausted runs remain inspectable; a new
campaign requires new explicit authorization.

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

`supported` means a recorded written argument passed review, not that Lean accepted
it. Research `root_proved` and `kernel_verified` remain false. Neither finite
computations nor local novelty establish an infinite theorem or literature priority.

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

A worker's `formalize` action saves a complete, revision-bound handoff. Its artifact
ID appears in status under `handoffs`. Initialize formalization without model calls:

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
the research request cap. Automated bidirectional formalization and a genuinely
shared budget across both systems remain follow-on work.

Other current limits: no automatic literature search, learned portfolio allocator,
cross-run method library, distributed execution, or empirical discovery-performance
claim. Verification so far uses offline scripted research and actual isolated
computations; paid model benchmarks require separate authorization.
