# Ensemble Prover User Guide

Start with a Lean theorem, a natural-language claim, or mathematical notes for
a longer project. Mini Prover searches for proofs and checks them with Lean.
The experimental NL frontends first translate the mathematics into Lean; the
formalization campaign can build definitions and supporting theorems across
multiple files before completing the root theorem.

This guide covers release 1.07, including both experimental NL frontends.
Older Mini-only releases do not include those modules.
Run commands from the repository root containing `.venv/` and `ensemble_prover/`,
not from inside the `ensemble_prover/` Python package. The live help is the
authority for the options available in your checkout:

```bash
.venv/bin/python -m ensemble_prover.mini_prover --help
.venv/bin/python -m ensemble_prover.nl_input --help
.venv/bin/python -m ensemble_prover.formalization --help
```

## 1. What you supply

Choose the entry point that matches your input:

| You have | Entry point | Instructions |
| --- | --- | --- |
| A Lean theorem, lemma, or conjecture in a Lake project | `ensemble_prover.mini_prover --lean-file ...` | [Lean theorem projects](#4-prepare-an-arbitrary-theorem-project) |
| A PutnamBench Lean file | `ensemble_prover.mini_prover --putnam-file ...` | [PutnamBench adapter](#5-use-the-putnambench-adapter) |
| One claim in natural language or LaTeX text | `ensemble_prover.nl_input` | [Single-claim translation](#18-formalize-one-natural-language-claim) |
| Longer mathematical notes needing definitions, lemmas, and resumable work | `ensemble_prover.formalization` | [Formalization campaigns](#19-run-a-multi-file-formalization-campaign) |

Every proof run needs a trusted, working Lean/Lake project and credentials for
the selected model provider. For direct Mini Prover input, also supply:

- a Lean source file containing the target theorem; and
- the target theorem's fully qualified name, except when using the optional
  PutnamBench adapter.

The NL frontends do not require you to write the target Lean declaration first.
They do still need an existing, built Lake project with Mathlib. Mini's
`--description` and `--description-file` add context to an existing Lean target;
they do **not** invoke translation. Lean remains the proof checker in every
workflow, and a checked proof does not certify the accuracy of an NL translation.

The release does not include Lean, Lake, Mathlib, PutnamBench, downloaded Lake
packages, or any theorem project. Supply those separately.

## 2. Install the runtime

### Requirements

- Linux
- a standard CPython 3.11 or 3.12 build
- `venv` support for that Python installation
- network access to the selected model provider
- a working Lean/Lake toolchain for the target project

The release audit is performed with CPython 3.11. The setup script accepts
standard CPython 3.11 and 3.12 and rejects trace-reference builds because the
runtime relies on the ordinary CPython object layout for exact rollback.

Clone the source checkout, or unpack a release archive, and enter its root:

```bash
git clone https://github.com/graviterra/ensemble-prover.git
cd ensemble-prover
```

Create the environment:

```bash
./scripts/setup_venv.sh
```

To select a particular interpreter:

```bash
PYTHON_BIN=python3.11 ./scripts/setup_venv.sh
```

The script creates `.venv/`, upgrades `pip`, and installs the pinned public
runtime lock from `requirements.txt`. The release runs in place from the source
checkout; the setup script does not install the package globally.

Confirm the installation:

```bash
.venv/bin/python -m pip check
.venv/bin/python -m ensemble_prover.mini_prover --help
```

Install Lean through the official [Lean installation
guide](https://lean-lang.org/install/). The target project's `lean-toolchain`
file controls the Lean version used by Lake. Confirm that project can resolve
its toolchain:

```bash
(cd /path/to/lake-project && lake env lean --version)
```

If that command fails, fix the theorem project before starting the prover.

## 3. Configure a provider

For a new installation, copy the environment template. Keep your existing
`.env` if you have already configured credentials:

```bash
cp .env.example .env
```

Set only the keys you use:

```dotenv
OPENAI_API_KEY=
DEEPSEEK_API_KEY=
OPENROUTER_API_KEY=
```

The CLI loads `.env` from the Ensemble Prover repository root. Do not commit
that file.

### Provider defaults

| Provider | CLI value | Default model | Required key |
| --- | --- | --- | --- |
| OpenAI | `openai` | `gpt-5.2` | `OPENAI_API_KEY` |
| DeepSeek | `deepseek` | `deepseek-v4-pro` | `DEEPSEEK_API_KEY` |
| OpenRouter | `openrouter` | none; specify one | `OPENROUTER_API_KEY` |

The default prover provider is DeepSeek. Select `--prover openai` explicitly
if only `OPENAI_API_KEY` is configured. OpenRouter always requires an explicit
`--prover-model` or `--refiner-model` using its routed model identifier.

The direct Mini Prover CLI has three independently configurable model roles:

- **Prover:** performs the ordinary proof search and is always present.
- **Refiner:** optionally takes over after prover stalls or rejected attempts.
- **Planner escalation:** repairs an empty or unparseable recursive plan.

Planner escalation defaults to `auto`. If `OPENAI_API_KEY` exists, `auto` uses
the OpenAI API with `gpt-5.6-terra`; otherwise it disables escalation with a
warning. Use `--planner-escalation off` to disable it deliberately, or choose
another provider and model explicitly.

The NL frontends have their own formalizer settings. The campaign currently
uses the OpenAI API for all three of its roles: `gpt-5.6-terra` for formalization
and independent review, and `gpt-5.6-luna` for proof search. See
[campaign model and budget controls](#campaign-models-and-budgets); Mini's
provider defaults above do not select the campaign's models.

### Provider examples

OpenAI prover:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --lean-file /path/to/lake-project/Target.lean \
  --theorem-name Example.target \
  --project-path /path/to/lake-project \
  --prover openai
```

DeepSeek prover and refiner:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --lean-file /path/to/lake-project/Target.lean \
  --theorem-name Example.target \
  --project-path /path/to/lake-project \
  --prover deepseek \
  --refiner deepseek
```

OpenRouter with explicit routed models:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --lean-file /path/to/lake-project/Target.lean \
  --theorem-name Example.target \
  --project-path /path/to/lake-project \
  --prover openrouter \
  --prover-model provider/model \
  --refiner openrouter \
  --refiner-model provider/model
```

Model availability, identifiers, prices, and reasoning controls are provider
contracts and may change. Confirm them with the provider before an expensive
run.

## 4. Prepare an arbitrary theorem project

`--lean-file` is the general interface. The project directory must exist and
contain `lakefile.lean` or `lakefile.toml`.

A minimal target file can look like this:

```lean
import Mathlib

namespace Example

theorem target (n : ℕ) : n + 0 = n := by
  sorry

end Example
```

Run it from the Ensemble Prover repository root:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --lean-file /path/to/lake-project/Target.lean \
  --theorem-name Example.target \
  --project-path /path/to/lake-project \
  --prover openai
```

The resolver locates the named declaration and extracts its statement and
reusable preamble. The target theorem's existing body is not treated as proof
evidence. The following inputs are rejected before search:

- a missing or non-`.lean` source file;
- a project with no Lake file;
- an empty or unknown theorem name;
- a private theorem target;
- `sorry` or `admit` in the target's type; or
- unsound `sorry` or `admit` dependencies in the reusable prefix.

Use a public wrapper theorem when the desired declaration is private.

### Imports and supporting source trees

Repeat `--import` to add modules to every target check:

```bash
--import Mathlib \
--import MyProject.Support
```

Repeat `--supporting-source-dir` when the theorem depends on source trees that
need to be indexed or made available to verification:

```bash
--supporting-source-dir /path/to/support/src \
--supporting-source-dir /path/to/another/library
```

Sources declared by the active Lake project are accepted directly. An external
support tree must belong to an identifiable Lake project. Preflight may build
that owning project automatically; verification proceeds only when the build
provides current `.olean` modules. A failed build or stale compiled environment
is rejected rather than silently added to Lean's search path.

### Natural-language context

Add a short description directly:

```bash
--description "Prove the result by reducing to a finite combinatorial lemma."
```

Or load UTF-8 text from a file:

```bash
--description-file /path/to/problem-description.txt
```

The two flags are mutually exclusive. Descriptions are sent to configured
model providers and should not contain secrets.
To start with prose instead of a Lean declaration, use one of the
[NL entry points](#1-what-you-supply).

## 5. Use the PutnamBench adapter

The adapter is optional and expects a separately installed compatible
PutnamBench checkout:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --putnam-file /path/to/PutnamBench/lean4/src/putnam_2025_a1.lean \
  --prover openai
```

The adapter can infer its Lake project from the source path and retains the
legacy first-theorem selection when `--theorem-name` is omitted.

Official answer values are hidden from model-facing prompts by default.
`--opaque-mode` is the default. Do not use `--visible-answer-mode`,
`--no-opaque-mode --allow-official-answer-visibility`, or equivalent
with-answer controls for answer-blind evaluation.

Successful proof files and graph pages contain the generated proof. Keep them
local when benchmark policy or an evaluation agreement prohibits publishing
answers. The public repository does not need those files to run the prover.

## 6. Control reasoning

The default reasoning mode is `provider-default`. It sends no explicit
reasoning field and lets the provider and model decide. This is not the same
as turning reasoning off.

Global controls:

```bash
--reasoning-mode provider-default
--reasoning-mode on --reasoning-effort high
--reasoning-mode off
```

Shortcuts:

```bash
--enable-reasoning
--disable-reasoning
```

Role-specific settings override the global settings:

```bash
--prover-reasoning-mode on \
--prover-reasoning-effort high \
--refiner-reasoning-mode off
```

Accepted effort values are `none`, `low`, `medium`, `high`, and `max`.
Provider support varies. Explicit controls are fail-closed: if a provider
rejects a required control, the request fails instead of silently dropping it.

Each run records the resolved reasoning configuration in `turns.jsonl` and
prints it before long model work. When a provider reports reasoning usage,
`reasoning_output_tokens=0` confirms that the successful response reported no
hidden reasoning tokens.

## 7. Set time and cost boundaries

The production defaults are intentionally patient. In particular, the default
overall worker, cumulative run, no-progress, and dollar budgets are all zero,
which means disabled. Set explicit limits before unattended or expensive runs.

Example bounded run:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --lean-file /path/to/lake-project/Target.lean \
  --theorem-name Example.target \
  --project-path /path/to/lake-project \
  --prover openai \
  --cost-budget-usd 10 \
  --mini-worker-timeout-s 7200 \
  --mini-run-wall-clock-budget-s 6900 \
  --mini-no-strong-progress-budget-s 1800
```

Replace those example limits with values appropriate for the theorem and
provider.

For an unattended run, the launcher supplies the same three time limits:

```bash
scripts/run_mini_unattended.sh \
  --lean-file /path/to/lake-project/Target.lean \
  --theorem-name Example.target \
  --project-path /path/to/lake-project \
  --prover openai --cost-budget-usd 10
```

Options supplied after the launcher override its preset limits, including
`0` to disable a limit. The ordinary CLI keeps its existing defaults. The
Putnam sweep uses its separate first-acceptance and second-acceptance deadlines;
this launcher does not change those milestones.

### Which timeout does what?

| Control | Scope |
| --- | --- |
| `--llm-timeout-s` | Default provider-call patience for prover and refiner |
| `--prover-timeout-s` | Prover role override |
| `--refiner-timeout-s` | Refiner role override |
| `--llm-request-timeout-s` | Shared HTTP response timeout; accepts seconds or `off` |
| `--prover-request-timeout-s` | Prover HTTP response override |
| `--refiner-request-timeout-s` | Refiner HTTP response override |
| `--lean-timeout-s` | One Lean check; default 300 seconds |
| `--mini-worker-timeout-s` | Hard parent-supervisor cap for the entire CLI worker |
| `--mini-run-wall-clock-budget-s` | Cumulative MiniSession wall-clock budget |
| `--mini-no-strong-progress-budget-s` | Active time without authoritative proof progress |
| `--mini-worker-startup-timeout-s` | Optional startup-handshake cap |
| `--mini-worker-shutdown-timeout-s` | Resource-shutdown cap; default 120 seconds |

`--llm-deadline-policy soft` is the default. It permits an in-flight model
generation to cross phase and retry deadlines while retaining the configured
HTTP-attempt watchdog. `hard` rejects a late model/tool-loop operation, but it
does not replace `--mini-worker-timeout-s` as an overall run cap.

Use `--lean-max-heartbeats` when a legitimate proof exceeds Lean's configured
heartbeat budget. Raising heartbeats does not raise `--lean-timeout-s`.

### Dollar budget

`--cost-budget-usd 0` disables dollar-budget stops but still records usage and
cost when the provider reports them. A positive budget performs pre-dispatch
reservations and requires known pricing for every configured paid role.

`--cost-budget-reserve-output-tokens` controls the output-token reserve used by
that pre-dispatch check. Final accounting prefers provider-reported usage.
Parallel sampling can multiply cost approximately with the number of samples.

## 8. Control search breadth

The ordinary defaults enable recursive planning, recursive helper proving,
proof-state scheduling, falsification, verified-helper caching, API search, and
federated mathematical retrieval. Start with the defaults and change one
family at a time.

### Direct turns and recursive work

| Option | Default | Meaning |
| --- | ---: | --- |
| `--max-prove-turns` | 30 | Direct prover conversation turns |
| `--max-refine-turns` | 25 | Refiner turns when a refiner is configured |
| `--mini-recursive-passes` | 6 | Recursive plan/prove/integrate passes |
| `--mini-recursive-claims` | 20 | Helper-plus-root claims across planner tranches |
| `--mini-recursive-turns-per-claim` | 6 | Model turns per recursive claim |
| `--recursive-helper-max-depth` | 3 | Child-session recursion depth |
| `--recursive-helper-max-attempts-per-node` | 2 | Child-session attempts for one node |
| `--recursive-helper-turns` | 5 | Turns in one child session |

Disable major lanes only for controlled experiments:

```bash
--no-mini-recursive
--no-recursive-helper-prover
--no-mini-falsification
--no-proof-state-engine
```

### Parallel samples

`--parallel-samples N` runs independent prove/refine samples concurrently.
The first Lean-accepted root wins, after which siblings receive
`--parallel-late-sample-grace-s` to preserve near-finished reusable evidence.

Use `--parallel-temps` for sample-level diversity:

```bash
--parallel-samples 2 --parallel-temps 0.3,0.7
```

Temperatures must be between 0 and 2 and are honored only by models that accept
temperature. Phase-specific temperatures remain enabled unless
`--no-mini-phase-temperatures` is supplied.

### Deterministic prepasses

The cold root tactic prepass and startup fast lane are opt-in:

```bash
--root-tactic-prepass
--startup-root-fast-lane
```

Their timeout and candidate controls bound the deterministic portfolios. They
are not overall run limits.

### Formal-state search

Bounded persistent formal-state search is disabled by default:

```bash
--formal-state-search
```

Its `--formal-state-search-*` options tune one resumable search quantum,
provider tactic generation, beam width, depth, candidates, backtracking, and
no-improvement retirement. Enable it deliberately; it adds Lean checks and may
add model calls.

## 9. Retrieval, tools, and caches

### Default retrieval behavior

- Mathlib API search is enabled.
- Federated mathematical retrieval is enabled.
- The active Lean project is indexed by default.
- Repair-time retrieval is enabled when API search is available.
- Eager premise retrieval is disabled; the model searches reactively.
- Proof-state retrieval as a separate scheduler action is disabled.

Useful controls:

```bash
--no-api-search
--no-mathematical-retrieval
--mini-retrieval-project-root /path/to/source/root
--mini-retrieval-cache-root /path/to/cache
--no-mini-retrieval-semantic
--no-mini-retrieval-dense
--proof-state-retrieval
--premise-retrieval --premise-retrieval-top-k 64
```

The retrieval index defaults to `runs/mini_retrieval/` in the Ensemble Prover
checkout. Use `--mini-retrieval-cache-root` to isolate it elsewhere.

The public dependency lock supports the core lexical and structural runtime.
Learned embeddings/rerankers, provider-specific tokenizers, and native SMT
backends are optional and are not installed by `setup_venv.sh`.

### Model tools

By default the model can:

- search Mathlib;
- check declaration names and types;
- test scratch proofs against Lean;
- evaluate bounded pure examples for exploration; and
- test whether a retrieved declaration applies to the active goal.

Disable individual tools with `--no-lean-check-tool`, `--no-try-lean-tool`,
`--no-compute-examples-tool`, or `--no-apply-decl-to-goal-tool`.
`--max-tool-calls-per-turn` caps tool calls inside one model turn.

Computed examples and falsification probes are observations, not proof
evidence. Only kernel-accepted artifacts cross the proof boundary.

### Persistent verified-helper cache

The proof-state cache is enabled by default. Same-problem helpers are
rechecked by Lean before being seeded into a new dossier. Its default file is
`runs/mini_prover_cache/verified_helpers.jsonl` in the Ensemble Prover
checkout.

```bash
--proof-state-cache-path /path/to/verified_helpers.jsonl
--no-proof-state-cache
```

Do not share a mutable cache between mutually untrusted users.

### Persistent Mini theory

Mini theory defaults to `build` mode and stores content-addressed verified
bundles under `~/.cache/mini_prover/theory`.

```bash
--mini-theory-mode build
--mini-theory-mode read
--mini-theory-mode off
--mini-theory-root /path/to/theory-store
--mini-theory-domain "algebra"
--mini-theory-bundle bundle_id
```

`read` imports compatible verified bundles without building missing theory.
`off` disables the facility. Repeat `--mini-theory-bundle` to request exact
bundle identifiers. Use `--mini-theory-promote-verified-helpers` only when you
intend generic verified helpers to be recompiled and published into the
persistent store.

## 10. Terminal output and run files

For the direct `mini_prover` CLI, without `--output-dir`, a run is written to:

```text
runs/mini_prover/<theorem>_<timestamp>/
```

Use a new directory for each run:

```bash
--output-dir /path/to/runs/example_target_01
```

The core files are:

| File | Purpose |
| --- | --- |
| `run.log` | Human-readable combined execution log |
| `turns.jsonl` | Append-oriented structured events, prompts, responses, tool calls, Lean checks, usage, and scheduler records |
| `activation_telemetry.json` | Aggregated subsystem-activation telemetry |
| `summary.json` | Terminal status, proof/export status, metrics, usage, and serialized proof dossier |
| `.lean_tmp/` | Local Lean scratch work for the run |

Additional local state may appear as features activate. Treat the entire run
directory as sensitive: it can contain theorem text, generated proofs, model
responses, provider metadata, and detailed failure feedback.

### Terminal trace levels

| Value | Behavior |
| --- | --- |
| `compact` | Default heartbeats, verdicts, and truncated assistant text |
| `full` | Readable trace with untruncated assistant responses |
| `jsonl` | Mirrors every structured event to the terminal |
| `off` | Disables structured live trace lines but still writes artifacts |

`off` is not a no-logging mode. The run files are still written.

## 11. Determine whether a run succeeded

The direct Mini Prover CLI exits with status 0 only when the final result crosses the required
verified export boundary. An unsolved run, infrastructure failure, or failed
solved export exits nonzero.

The NL CLIs have different completion meanings: `nl_input --formalize-only`
can exit 0 with an unproved, typechecked translation, and a campaign can exit 0
after a normal bounded pause. For campaigns, inspect the JSON `status` and
`stop_reason`, then explicitly export a `proved` project; see
[campaign status and recovery](#campaign-status-and-recovery).

For automation, inspect `summary.json` rather than parsing terminal banners.
A trustworthy solved result should report the run as solved and the solved
export as verified. A root candidate that failed reconstruction, fresh Lean
replay, or axiom audit is not a completed exported solve.

The terminal may show:

- `SOLVED`: the root and export boundary completed;
- `DISPROVED`: Lean accepted an audited proof of the negation;
- `NOT SOLVED`: search ended without a verified root;
- `INFRASTRUCTURE ABORTED`: the run ended without a mathematical verdict; or
- `ROOT FINALIZED, EXPORT PENDING`: a supervised internal path finalized the
  root but delegated export to its parent process.

Do not treat model prose or a displayed candidate proof as sufficient. Check
the terminal summary and `summary.json`.

## 12. Standalone exports and proof graphs

On an ordinary successful CLI run, Ensemble Prover reconstructs a standalone
Lean source artifact under:

```text
runs/mini_prover/solved/
```

Here, "standalone" means one reconstructed source file. The artifact retains
its project imports and still requires the recorded or a compatible Lake
environment; it does not bundle Lean or its dependency closure.

The exporter performs fresh Lean verification and an axiom audit before the
result counts as a completed solved export. PutnamBench-adapter exports also
attempt to write local navigation artifacts automatically under:

```text
runs/mini_prover/solved/depgraphs/
```

For each graphed theorem, the graph set includes:

- `<name>.html` — interactive dependency/proof graph;
- `<name>.json` — graph data;
- `<name>.source.html` — navigable rendered Lean source; and
- `<name>.source_map.json` — declaration/source mapping.

The explicit directory-wide graph command below also writes an `index.html`
page listing the generated graphs.

To rebuild all eligible local solved exports (including automatic graph
generation for PutnamBench-adapter exports):

```bash
.venv/bin/python -m ensemble_prover.extract_solved
```

To generate or regenerate graph files for generic and adapter exports in an
existing local solved directory:

```bash
.venv/bin/python -m ensemble_prover.export_dependency_graph \
  --solved-dir runs/mini_prover/solved
```

To audit existing exports again:

```bash
.venv/bin/python -m ensemble_prover.extract_solved --audit-existing
```

The exporter offers `--skip-lean-verify` for specialized internal workflows.
Do not use it when producing a result that will be described as verified.

These exports contain answers. Keep them out of public repositories when the
source benchmark or evaluation agreement restricts answer publication.

## 13. Replay and interruption behavior

The direct Mini Prover CLI writes durable attempt checkpoints by default.
After stopping a run, continue its latest generation into a new output directory:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --resume-from runs/mini_prover/example_target_01 \
  --output-dir runs/mini_prover/example_target_02
```

Omit `--output-dir` to allocate a new directory automatically. Resume inherits
the original input, models, parallel sample count, and search and cost limits.
Explicit policy overrides must match the saved values; terminal trace settings
and the new output directory may change. `--no-checkpoint` disables persistence
for a new run. Older `--mini-resume` and branch/fork flag names are not supported.

The saved state includes committed conversations, accepted helpers, proof work,
recursive child frames, planner results, and the shared cost ledger. Each
parallel sample resumes its own lane. Saved proofs pass fresh Lean checks
before they regain authority. A process or HTTP request itself cannot be
restored: unfinished work resumes from its durable boundary. Committed planner
results are consumed without repeating their provider request; uncertain
in-flight provider exposure remains charged against the attempt's cost limit.

Verified theory bundles installed during the run are regenerated from the
current library on restore. Their recorded source snapshot and the initial
configured context must match. An incomplete final diagnostic trace row beyond
the validated checkpoint prefix is retained in the predecessor file and
excluded from restored trace metrics; corruption of committed evidence still
rejects restart.

Resume requires the same input, executor source, and material Lean environment.
An incompatible or incomplete checkpoint is rejected before search resumes.
Only the latest generation can continue, with one active writer per attempt.
Previous generation artifacts remain unchanged. Keep the generation directories
and their sibling `.mini_attempts` directory together at their recorded paths;
the latter contains the shared attempt head and financial journal. A run log or
`turns.jsonl` alone is not a resumable checkpoint.

Worker time is cumulative across generations and shared across samples. A clean
stop excludes the subsequent stopped interval. After an abrupt exit, the
unobserved interval since the last checkpoint is conservatively counted through
restart, because its active and stopped portions cannot be distinguished.
Restart does not reset cost, recovery, or worker allowances. An exhausted
attempt requires a new run with explicitly chosen limits.

Legacy runs without `attempt_checkpoint.json` cannot resume their exact search.
Start a new run to reuse compatible verified cache and Mini-theory evidence
through the public cache interfaces.

Provider-free diagnostic replay is supported:

```bash
.venv/bin/python -m ensemble_prover.mini_session.replay \
  runs/mini_prover/example_target_01
```

Emit JSON:

```bash
.venv/bin/python -m ensemble_prover.mini_session.replay \
  runs/mini_prover/example_target_01 \
  --json
```

Replay supported repair-next-action decisions:

```bash
.venv/bin/python -m ensemble_prover.mini_session.replay \
  runs/mini_prover/example_target_01 \
  --replay-decisions
```

Classify recent runs beneath a run root:

```bash
.venv/bin/python -m ensemble_prover.mini_session.replay \
  runs/mini_prover \
  --recent 10
```

Diagnostic replay explains recorded behavior; it does not ask a provider to
continue proof search.

The formalization campaign has a separate durable project ledger. Repeating
`formalization run` resumes that project and reuses verified components; it
does not restore every internal Mini search state. See
[the campaign workflow](#19-run-a-multi-file-formalization-campaign).

For a graceful stop, send one interrupt and allow cleanup to finish. Repeated
signals may escalate before all terminal artifacts are flushed.

## 14. Troubleshooting

### The selected provider key is missing

Symptom:

```text
DEEPSEEK_API_KEY is not set in the environment.
```

The default prover is DeepSeek. Either set that key or select the provider for
the key you configured:

```bash
--prover openai
```

### OpenRouter requires a model

Pass a routed identifier:

```bash
--prover openrouter --prover-model provider/model
```

### Planner escalation warns that it is disabled

`--planner-escalation auto` found no `OPENAI_API_KEY`. This does not disable
the main prover. Set the key, choose an explicit escalation provider/model, or
pass `--planner-escalation off`.

### The theorem cannot be found

Use the fully qualified Lean name, including namespaces. Confirm it with the
target project:

```bash
(cd /path/to/lake-project && lake env lean /path/to/Target.lean)
```

### Target elaboration fails before proof search

Check that:

- the target file belongs to the supplied Lake project;
- all imports resolve under that project's pinned toolchain;
- the theorem is not private;
- the reusable prefix contains no `sorry` or `admit`; and
- each external support tree has an owning Lake project whose preflight build
  can complete.

### Lean checks time out

Raise the operation cap and, independently, the heartbeat allowance:

```bash
--lean-timeout-s 600 --lean-max-heartbeats 3200000
```

First confirm the target also elaborates outside the prover. Higher limits do
not repair a broken project or a nonterminating tactic.

### A provider call appears stuck

Set finite request and overall bounds:

```bash
--llm-request-timeout-s 600 \
--mini-worker-timeout-s 7200
```

Remember that provider retries may begin a new HTTP attempt. Use the overall
worker limit when wall-clock predictability matters.

### The run stopped on cost

Read usage and reservation events in `turns.jsonl` and the totals in
`summary.json`. Increase the budget only after confirming model pricing and
the expected effect of parallel samples and planner escalation.

### Export failed after a root proof was found

Inspect the solved-export fields and diagnostic preview in `summary.json`.
Common causes include reconstruction failure, project drift, Lean rejection,
or an axiom-audit failure. The run is not a completed exported solve until the
export is independently verified.

### Semantic retrieval extras are unavailable

The minimal public lock intentionally omits learned embedding and reranking
packages. Disable the optional lane with `--no-mini-retrieval-semantic`, or
install a compatible optional stack in a separate environment after reviewing
its resource and licensing requirements.

## 15. Security, privacy, and operational safety

Ensemble Prover executes Lean and local subprocesses. Run untrusted theorem
projects only inside an appropriately isolated operating-system environment.

Provider API keys and a denylist of common token, secret, password,
private-key, cloud-identity, auth-config, and credential-bearing URL variables
are stripped from Lean, Lake, solvers, Git, and other local-tool child
environments. The trusted internal Python worker that calls configured model
providers retains the keys it needs. On Linux, credential-bearing parent and
watchdog processes are marked non-dumpable before they spawn children, blocking
descendant access to their `/proc/<pid>/environ` data.

This credential filtering is not an operating-system sandbox. A hostile
theorem project still executes with the prover user's filesystem and network
privileges and may read credentials stored in accessible files. Use a
disposable container or virtual machine for untrusted Lean code, expose only
the minimum required files and key, restrict network access, and revoke the
key after the run. Python virtual environments do not provide this isolation.

Configured providers may receive:

- the theorem statement and reusable Lean context;
- the optional natural-language description;
- original NL source passages, supporting definitions, proof plans, and reviewer
  evidence when using the NL frontends;
- retrieved declarations;
- generated proof attempts; and
- structured Lean error feedback.

Do not submit confidential mathematics or source code to an external provider
unless its terms and your authorization permit it.

Run directories, verified-helper caches, retrieval indexes, theory stores, and
solved exports can contain sensitive proof material. The persistent defaults
are `runs/mini_prover_cache/verified_helpers.jsonl`, `runs/mini_retrieval/`,
and `~/.cache/mini_prover/theory`. Protect, separate, and delete them according
to the applicable data policy. Never commit `.env`, provider credentials, or
generated run artifacts.

Only Lean-accepted and freshly exported artifacts should be described as
proved. Plans, model output, retrieval hits, computed examples, speculative
claims, and counterexample probes are search evidence until they cross the
relevant verification gate.

## 16. Public CLI option map

The following map covers the `mini_prover` option families without duplicating the
live help text. Run `--help` for exact defaults, allowed values, and detailed
semantics. These flags are not automatically accepted by the separate campaign
CLI.

### Help

`-h`, `--help`

### Input and project

`--lean-file`, `--putnam-file`, `--theorem-name`, `--project-path`,
`--lean-project-dir`, `--import`, `--supporting-source-dir`, `--source-dir`,
`--description`, `--description-file`

### Providers, roles, and reasoning

`--prover`, `--prover-model`, `--refiner`, `--refiner-model`,
`--planner-escalation`, `--planner-escalation-model`, `--reasoning-mode`,
`--enable-reasoning`, `--disable-reasoning`, `--reasoning-effort`,
`--prover-reasoning-mode`, `--prover-reasoning-effort`,
`--refiner-reasoning-mode`, `--refiner-reasoning-effort`

### Provider, Lean, wall-clock, and dollar budgets

`--llm-timeout-s`, `--prover-timeout-s`, `--refiner-timeout-s`,
`--llm-request-timeout-s`, `--prover-request-timeout-s`,
`--refiner-request-timeout-s`, `--llm-deadline-policy`,
`--max-prove-turns`, `--max-refine-turns`, `--cost-budget-usd`,
`--cost-budget-reserve-output-tokens`, `--lean-timeout-s`,
`--lean-max-heartbeats`, `--mini-worker-timeout-s`,
`--mini-run-wall-clock-budget-s`, `--mini-no-strong-progress-budget-s`,
`--mini-worker-startup-timeout-s`, `--mini-worker-shutdown-timeout-s`,
`--mini-hard-operation-watchdog`

### Output and trace

`--output-dir`, `--terminal-trace`, `--raw-feedback`

### Retrieval and model tools

`--api-search`, `--no-api-search`, `--mathematical-retrieval`,
`--no-mathematical-retrieval`, `--mini-retrieval-project-root`,
`--mini-retrieval-include-lean-project`,
`--no-mini-retrieval-include-lean-project`, `--mini-retrieval-cache-root`,
`--no-mini-retrieval-semantic`, `--mini-retrieval-dense`,
`--no-mini-retrieval-dense`, `--no-mini-retrieval-type-directed`,
`--no-lean-check-tool`, `--no-try-lean-tool`,
`--no-compute-examples-tool`, `--no-apply-decl-to-goal-tool`,
`--max-tool-calls-per-turn`, `--premise-retrieval`,
`--no-premise-retrieval`, `--premise-retrieval-top-k`,
`--premise-zero-hit-policy`, `--premise-zero-hit-max-local-turns`,
`--premise-zero-hit-keep-library-first`,
`--premise-zero-hit-no-api-grounding-escape`

### Proof-state scheduling and formal search

`--proof-state-retrieval`, `--no-proof-state-retrieval`,
`--no-repair-retrieval`, `--repair-retrieval-top-k`,
`--no-proof-state-engine`, `--no-proof-state-child-tactics`,
`--proof-state-child-tactic-timeout-s`,
`--proof-state-child-tactic-max-candidates`,
`--proof-state-child-goal-limit`, `--proof-state-decl-application-limit`,
`--proof-state-batch-parallelism`, `--formal-state-search`,
`--no-formal-state-search`, `--formal-state-search-timeout-s`,
`--formal-state-search-operation-timeout-s`,
`--formal-state-search-provider-timeout-s`,
`--formal-state-search-provider-max-tokens`,
`--formal-state-search-provider-reasoning-effort`,
`--formal-state-search-provider-max-attempts`,
`--formal-state-search-provider-retry-backoff-s`,
`--formal-state-search-beam-width`, `--formal-state-search-max-steps`,
`--formal-state-search-max-candidates`,
`--formal-state-search-backtrack-limit`,
`--formal-state-search-max-no-improvement-quanta`

### Falsification and verified caches

`--mini-falsification`, `--no-mini-falsification`,
`--mini-falsification-max-checks`,
`--mini-falsification-operation-timeout-s`,
`--mini-falsification-engine-timeout-s`, `--proof-state-cache`,
`--no-proof-state-cache`, `--proof-state-cache-path`

### Putnam answer visibility

`--opaque-mode`, `--no-opaque-mode`, `--allow-official-answer-visibility`,
`--visible-answer-mode`

### Parallelism and temperature

`--parallel-samples`, `--parallel-late-sample-grace-s`, `--parallel-temps`,
`--mini-phase-temperatures`, `--no-mini-phase-temperatures`,
`--mini-temperature-planner`, `--mini-temperature-initial-proof`,
`--mini-temperature-formalization-helper`, `--mini-temperature-lean-repair`,
`--mini-temperature-refine`, `--mini-temperature-route-assembly`,
`--mini-temperature-stagnation-escape`,
`--mini-temperature-initial-use-sample`,
`--mini-temperature-initial-no-sample`

### Deterministic and recursive search

`--root-tactic-prepass`, `--no-root-tactic-prepass`,
`--root-tactic-timeout-s`, `--root-tactic-max-candidates`,
`--startup-root-fast-lane`, `--no-startup-root-fast-lane`,
`--startup-root-fast-lane-tactic-timeout-s`,
`--startup-root-fast-lane-tactic-max-candidates`, `--mini-recursive`,
`--no-mini-recursive`, `--no-adaptive-recursive-on-stall`,
`--mini-recursive-passes`, `--mini-recursive-claims`,
`--mini-recursive-turns-per-claim`, `--mini-recursive-tactic-timeout-s`,
`--mini-recursive-tactic-max-candidates`, `--recursive-helper-prover`,
`--no-recursive-helper-prover`, `--recursive-helper-budget`,
`--recursive-helper-max-depth`, `--recursive-helper-max-attempts-per-node`,
`--recursive-helper-turns`, `--recursive-helper-refine`,
`--no-recursive-helper-refine`

### Persistent Mini theory

`--mini-theory-mode`, `--mini-theory-root`, `--mini-theory-domain`,
`--mini-theory-bundle`, `--mini-theory-verifier-timeout-s`,
`--mini-theory-operation-timeout-s`,
`--mini-theory-promote-verified-helpers`

## 17. A practical first-run checklist

For a direct Mini Prover run, before starting:

1. `pip check` passes in `.venv`.
2. `lake env lean --version` works in the target project.
3. The target file elaborates in that project.
4. The fully qualified theorem name is correct.
5. The selected provider key and model are configured.
6. Explicit cost and overall wall-clock limits are set when needed.
7. The output directory is new and writable.
8. The theorem and description are permitted to be sent to the provider.
9. The target project is trusted with the provider key, or the run is contained
   in a disposable environment with a restricted credential.

After the run:

1. Check the process exit status.
2. Read `summary.json`.
3. Require a verified solved-export status before calling the result solved.
4. Open the local dependency graph when one was generated.
5. Keep run artifacts and proof exports private when required.

## 18. Formalize one natural-language claim

After [installation](#2-install-the-runtime) and
[provider setup](#3-configure-a-provider), translate and prove a small claim:

```bash
.venv/bin/python -m ensemble_prover.nl_input \
  --text 'For every natural number n, n + 0 = n.' \
  --project-path lean_project \
  --formalizer openai --formalizer-model gpt-5.6-terra \
  -- --prover openai --prover-model gpt-5.6-luna
```

This uses `OPENAI_API_KEY` for both roles and makes paid model requests.
Replace `lean_project` with the path to your own built Lake/Mathlib project;
no project is bundled with this release. Text
after `--` is passed to Mini; explicitly selecting the prover avoids accidentally
using Mini's default DeepSeek provider.

For a longer claim, save the complete statement and assumptions in a UTF-8
file and replace `--text ...` with `--text-file my_claim.md`. LaTeX is read as
text, not compiled. Use `--context-file ResearchContext.lean` for trusted Lean
definitions and repeated `--import MyProject.Background` for project libraries.

To inspect a translation before spending on proof search:

```bash
.venv/bin/python -m ensemble_prover.nl_input \
  --text 'For every natural number n, n + 0 = n.' \
  --project-path lean_project \
  --output-dir runs/nl_input/nat_identity_review \
  --formalize-only
```

The output directory must be new. Review `Problem.lean` and `formalization.json`
in that directory. The theorem still has a `sorry` proof slot: exit 0 here means
the translation passed Lean type checking, **not** that a proof was found.
Do not combine `--formalize-only` with arguments after `--`.

Prove the unchanged saved translation without another formalizer request:

```bash
.venv/bin/python -m ensemble_prover.nl_input \
  --prove-existing runs/nl_input/nat_identity_review \
  -- --prover openai --prover-model gpt-5.6-luna
```

This validates saved artifacts and starts a new Mini attempt; it is not a
search-checkpoint resume. Mini writes its own proof run and verified export.
If the translation is wrong or a clarification is needed, submit corrected,
self-contained input as a new run rather than editing saved artifacts.

This frontend labels translations `machine_proposed`; it has no independent
semantic reviewer. For iterative multi-file theory development and independent
model review, use the campaign below. See [the single-claim guide](nl_input.md)
for all options, saved files, and limitations.

## 19. Run a multi-file formalization campaign

Use this workflow for notes, conjectures, or longer arguments that need new
definitions and supporting proofs. You supply documents and an objective;
the controller decomposes the work, reviews proposed statements, proves tasks
with Mini, and checks separately compiled Lean modules.

### Initialize, run, and inspect

Start with the included finite-difference example and `OPENAI_API_KEY` in the
repository-root `.env`. Replace `lean_project` below with your own built
Lake/Mathlib project; the release includes the example text, not a Lean project:

```bash
.venv/bin/python -m ensemble_prover.formalization init \
  --project-path lean_project \
  --source examples/formalization/finite_differences.md \
  --goal 'Formalize and prove the complete theorem in the supplied document.' \
  --output runs/formalization/finite_difference_example

.venv/bin/python -m ensemble_prover.formalization run \
  runs/formalization/finite_difference_example \
  --max-steps 20 --max-model-calls 60

.venv/bin/python -m ensemble_prover.formalization status \
  runs/formalization/finite_difference_example

.venv/bin/python -m ensemble_prover.formalization task \
  runs/formalization/finite_difference_example root
```

`init` saves input and the environment snapshot without making model requests;
`run` performs paid model work. The chosen 20-step/60-request invocation is a
starting allowance, not a promise to finish the example. Repeat the same `run`
command to continue. Do not rerun `init` on an existing campaign directory.

For your own problem, replace the example with `--source my_problem.md` and
write the desired theorem in `--goal`. State the domains, quantifiers,
assumptions, definitions, and desired conclusion explicitly. Include a proof
sketch when available. Repeat `--source` for more files and `--import` for
trusted, already-built project modules. Input files must be UTF-8 text:
plain prose, Markdown, LaTeX source, or text extracted from papers. PDF/image
extraction, URL downloading, and literature acquisition are not implemented.

Sources are saved immutably at initialization; editing the original file later
does not update the campaign. Use `revise` for corrected task instructions, or
start a new campaign to use a changed source collection.

### Campaign models and budgets

The campaign CLI currently routes all roles through the OpenAI API. These are
its defaults, independent of the Mini provider defaults:

```bash
.venv/bin/python -m ensemble_prover.formalization run \
  runs/formalization/finite_difference_example \
  --formalizer-model gpt-5.6-terra \
  --reviewer-model gpt-5.6-terra \
  --prover-model gpt-5.6-luna \
  --max-steps 20 --max-model-calls 60
```

| Option | Meaning |
| --- | --- |
| `--max-steps` | Controller steps for this invocation; default 100. |
| `--max-model-calls` | Formalizer/reviewer requests for this invocation; default 300. It excludes nested Mini calls and individual transport retries. |
| `--model-timeout-s` | Seconds per model operation, including retries; omitted uses shared model defaults. |
| `--lean-timeout-s` | Lean operation timeout; default 300 seconds. |
| `--lease-s` | Worker lease duration, renewed while running; default 300 seconds. It is not a whole-run timeout. |

These limits are **not dollar spending caps or whole-campaign wall-clock
limits**. The campaign has no CLI pass-through for Mini's `--cost-budget-usd`,
`--prover`, or other Mini flags; use only options shown by
`formalization run --help`. To stop, interrupt once and allow cleanup, then
resume with `run` when ready.

No smaller campaign-specific text/output cap is imposed. Provider limits still
apply. Required plans and evidence are preserved through Mini and recursive
helper calls; a request that cannot fit pauses explicitly instead of silently
shortening the mathematics.

### Campaign status and recovery

Commands print JSON. Check `status` and any `stop_reason`, not just the exit
code:

| Result | What to do |
| --- | --- |
| `status: proved` | The root and its reachable compiled module dependencies validate. Export next. |
| `status: paused`, without a provider/context error | Normal bounded or temporarily unavailable work; inspect and repeat `run` to continue. Exit 0 does not mean proved. |
| `stop_reason: provider_error` | Resolve the credential/provider problem before resuming. The CLI exits nonzero. |
| `stop_reason: context_overflow` | Inspect the affected task; choose a model with sufficient context or revise/decompose the task. Blind retries cannot make the same prompt smaller. |
| `status: needs_clarification` or `blocked` | Inspect the task's saved question/error and revise the affected task. |
| `status: invalid`, or an environment validation error | Do not trust completion. Inspect changed/missing artifacts or dependencies; never replace the recorded fingerprint to bypass the check. |

Inspect `root` first. If the issue belongs to a supporting task, use its task ID
with `task` and `revise`. Supply the full corrected instructions, not just a
short answer that omits the original objective:

```bash
.venv/bin/python -m ensemble_prover.formalization revise \
  runs/formalization/finite_difference_example root \
  --description 'Prove the stated commutation theorem for arbitrary abelian groups A and B and arbitrary functions f; do not assume f is additive.'
```

Revision invalidates that task and its dependents. Completed unrelated work is
retained. Restarting a project reuses verified components and matching saved
proof source; it does not reconstruct every prior Mini search graph.

Keep the installed Lean/Mathlib environment unchanged while running. Generated
output directories must be separate from base compiled/search roots, and base
libraries must not import the reserved `Formalization` module namespace. Older
snapshots without current provenance records fail closed; start a new campaign
rather than rewriting their trust metadata.

### Export and read the results

Once `status` reports `proved`, export to a new directory:

```bash
.venv/bin/python -m ensemble_prover.formalization export \
  runs/formalization/finite_difference_example \
  --output runs/formalization/finite_difference_example_export
```

The bundle contains Lean modules, `Root.lean`, original documents, an environment
record, and a `README.md` with the replay command. Existing export directories
are not overwritten. Replay still requires the recorded Lake/Mathlib
environment; this is not a vendored dependency bundle.

The campaign directory contains `project.sqlite3` (tasks and dependency state),
`sources/` (original documents), `blobs/` (content-addressed records), `modules/`
(checked Lean artifacts), and `proof_runs/` (Mini attempt dossiers). Treat all
of it as private if your mathematics is private.

Independent model review helps assess translation fidelity but is not a
certificate that the Lean statement means the intended mathematics. Read the
generated definitions and theorem before relying on the result. The system has
real-Lean integration and live-example evidence; autonomous frontier success
rates and FLT/million-line performance have not been established. See the
[advanced campaign guide](formalization-campaign.md) for export replay,
concurrent workers, and environment recovery.
