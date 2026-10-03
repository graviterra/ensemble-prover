# Operating and recovering proof work

The most useful run diagnosis separates three questions: what mathematical work
was established, whether the process is making operational progress, and which
resource or permission currently limits the next action.

## Before a long run

1. Build the intended Lean/Lake project and check the selected declaration.
   `mini_prover ... --check-input` performs local input preparation without model
   calls. It does not test provider authentication.
2. Select provider roles explicitly. A configured API key, installed CLI, or
   local profile is not proof of a working model request.
3. Set limits appropriate to the workflow. For subscription roles, bound time
   and requests rather than relying on API dollar accounting.
4. Use a new output directory and preserve the project and dependency build if
   you will need to resume.
5. Review the formal statement. A perfectly checked proof of a mistranslated
   proposition does not answer the intended question.

## Budgets are layered

| Control | What it bounds | What it does not imply |
| --- | --- | --- |
| Provider request/deadline controls | A model operation or its adapter's request handling | Overall proof-search runtime |
| Lean timeout and heartbeats | Individual checks and elaboration effort | A mathematical verdict after timeout |
| Conversation, recursive, and tactic limits | Work within a particular search lane | A new budget for each child |
| Mini worker/run/no-strong-progress limits | Different overall or inactivity windows | Identical clocks; see the detailed timeout reference |
| API dollar cap | Accounted and reserved API usage | Pricing of subscription allowance or zero-cost local compute |
| Local inference allocation | Finite shared dispatch/output/request-time allowances | Exclusive GPU ownership or cancellation of remote generation |
| Sweep acceptance deadlines | Minimum timely accepted progress on each attempt | Time allowed for the entire sweep |
| Discovery request and elapsed limits | Shared authorization for its integrated research and proof workflow | A reset on resume or a cap on an independently launched campaign |

See [Mini timeout semantics](USER_GUIDE.md#which-timeout-does-what),
[local compute budgets](local-inference.md#bound-shared-compute-independently-of-api-cost),
and [discovery budgets](USER_GUIDE.md#research-budgets-and-recovery).
An output-token reservation used for cost accounting does not change the model's
output allowance. Missing usage remains unknown rather than becoming free work.

Model calls that repair ill-typed planner statements use the configured provider
deadline policy. The Lean tactic timeout bounds the subsequent formal check,
not model generation. Aggregate repair-call limits and enclosing run cancellation
still apply, including when the provider deadline policy is soft.

Fresh root-assembly conversations can receive the prover's earlier rejected
proof and Lean diagnostics when the target, environment, answer policy and
existing helper sources still match. This feedback describes failed code, not
a false mathematical claim. It also flags research advice that repeats the
rejected steps as needing correction or another check.

An unknown name bound by a leading `have` or `let` inside the target is routed
to local proof-shape repair. Such a label may disappear when Lean reduces the
target; it is not necessarily a library declaration available to API search.

Startup events include a `verified_helper_cache` stage with wall time and process
CPU time. This stage is nested within proof-session initialization; do not add
its duration to that containing stage when calculating total startup time.

## Read the mathematical and operational status together

In the browser, inspect **Mathematical focus**, **Runtime evidence**, and
**Graph & evidence**. The focus names the selected obligation and recorded reason
for dispatch. Runtime settings come from the attempt's recorded source and
requests, which can differ from the currently running interface server.

| Observation | Interpretation |
| --- | --- |
| Helper accepted | That helper's statement was checked; inspect its relation to the root |
| Root internally solved | Proof search produced an accepted root candidate; export may remain pending |
| Export verified | Reconstructed source passed fresh verification and axiom checks for the recorded target |
| Certified negation | The exact recorded claim was refuted; check whether it is the root, a helper, or an answer candidate |
| Research supported/refuted | An argument received review; this is distinct from a Lean certificate |
| Infrastructure aborted | Search did not reach a mathematical solved/unsolved conclusion |
| Quiet event stream | No recent recorded event; not enough evidence to call the run hung |

The browser results library is a bounded view, not a complete benchmark
scorecard. Closing a browser tab does not stop a worker. **Pause updates** pauses
observation, not computation.

## Files worth keeping

| Artifact | Use |
| --- | --- |
| `summary.json` | Terminal outcome, export status, usage, and proof dossier |
| `turns.jsonl` and `run.log` | Structured action evidence and readable execution history |
| `activation_telemetry.json` | Recorded subsystem activity |
| `attempt_checkpoint.json` | Generation identity and link to durable attempt state |
| Sibling `.mini_attempts/` | Shared checkpoint head and accounting journal needed for resume |
| Answer preparation directory | Original question, proposed answer, reviews, and proof plan |
| `runs/mini_prover/solved/` | Reconstructed saved exports and optional graph/presentation artifacts |
| Research/campaign directories | Their independent ledgers, source documents, reviews, and proof handoffs |

Keep generation directories and `.mini_attempts` together at their recorded
paths. A log copied on its own cannot restore a run. Logs, catalogs, and checkpoints
can contain private mathematics and model responses.

## Stop and resume

Send one interrupt and allow cooperative cleanup, or use the confirmed stop
control for a browser-owned attempt. A stop request is not confirmation that all
processes have exited. Repeated interrupts can escalate before artifacts finish
writing.

Resume the latest Mini generation into a new output directory:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --resume-from /path/to/previous-attempt \
  --output-dir /path/to/new-attempt
```

Resume retains input, models, search policy, accounting, and accumulated worker
time. It rechecks saved mathematical evidence and refuses incompatible state.
It does not reset exhausted limits. Missing checkpoints, interrupted answer
preparation, and logs from older noncheckpointed runs are not exact resumable
searches.

An executor source change requires the explicit
`--resume-accept-source-hash` procedure described in the
[recovery reference](USER_GUIDE.md#13-replay-and-interruption-behavior). That
acknowledgment does not approve changed mathematics, dependencies, or checkpoint
formats. Never edit checkpoint identities to force acceptance.

Other workflows resume differently:

| Workflow | Continue with |
| --- | --- |
| Mini attempt | `mini_prover --resume-from PREVIOUS` |
| Sweep | The sweep launcher's saved-manifest resume command |
| Formalization campaign | Repeat `formalization run DIRECTORY` with its invocation limits |
| Autonomous discovery | Repeat `research_claims discovery run DIRECTORY` within saved authorization |
| Stopped Mini needing a new research investigation | `./research /path/to/stopped-run`; this creates a separate research workflow |

Use the [sweep guide](../ensemble_prover/PUTNAM_SWEEP.md) for exact resume syntax
and acceptance cutoffs. By default it requires one accepted proof/helper by
1,200 seconds and a second distinct acceptance by 1,800 seconds from worker
readiness, with a separate startup cap. Those acceptances are not necessarily
root solves. A research note does not satisfy the gate.

## Diagnose a slow or failed attempt

Start with the latest complete events and the terminal summary. Identify the
active scope, action, provider request, and governing deadline before changing
settings.

| Symptom | Useful next check |
| --- | --- |
| Long answer preparation | Inspect proposal/review stage; proof search has not necessarily started |
| Many helpers, no root | Inspect live route blockers and whether accepted consumers use those helpers |
| Root found, export still running | Inspect fresh replay, dependency reconstruction, axiom audit, and presentation status |
| Provider protocol incompatibility | Check adapter/CLI compatibility; do not interpret it as failed mathematics |
| Quota or authentication rejection | Correct account access, then explicitly resume where supported |
| Lean cancellation or generation replacement | Inspect the operation deadline and subsequent work; replacement alone does not prove a process leak |
| Unsettled subprocess transport warning | Async exit notification may lag OS exit; the warning alone does not establish a live child or a network cause |
| Local capacity remains occupied | Inspect unknown-completion records and reconcile with actual server evidence |
| Memory empty or unavailable | Check mode, catalog root, eligibility, source authority, and remaining allocation |
| Stop before expected Mini timeout | Inspect the outer sweep policy or supervisor limits |

Use provider-free replay to inspect recorded decisions:

```bash
.venv/bin/python -m ensemble_prover.mini_session.replay /path/to/attempt --json
```

Replay does not continue proving or contact a provider. For a useful issue report,
include the recorded source version, launch settings, target/environment identity,
failure kind, and a relevant event interval, after removing private source and
credentials. Do not infer uninterrupted event-loop blocking from timestamp gaps
alone.

## Verify and share a result

Inspect the exact exported theorem and verification status, then replay against
the recorded or compatible project. A standalone source file still depends on
its imports and toolchain. `extract_solved --audit-existing` rechecks saved
exports; proof graph generation is navigation, not an independent certificate.

Review the [export guide](USER_GUIDE.md#12-standalone-exports-and-proof-graphs),
[evaluation scope](RESULTS.md), and source licensing or benchmark answer policy
before sharing artifacts. Keep the browser on localhost with trusted projects
and state directories; see [security](../SECURITY.md).
