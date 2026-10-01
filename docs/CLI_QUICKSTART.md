# Command-line workflows

Use these examples to run Ensemble Prover from a terminal. For the browser
workspace, start with the [homepage](../README.md#quick-start) or
[browser setup guide](../interface/README.md).

Run commands from the repository root. The [User Guide](USER_GUIDE.md) explains
providers, budgets, project setup, exports, and recovery in detail.

## Install the CLI

### Requirements

- Linux
- Standard CPython 3.11 or 3.12
- Lean toolchain compatible with the target Lake project
- An API key for the selected provider, or a ChatGPT Codex / Claude Code
  subscription sign-in for Mini's prover and refiner

The manual research ledger needs neither Lean nor provider credentials.
Autonomous research uses the OpenAI API or Codex subscription sign-in and does not need Lean until the
formalization handoff. Optional Python experiments require Linux bubblewrap
with usable unprivileged user namespaces; there is no unsandboxed fallback.

The public runtime snapshot pins the complete dependency closure for four core
Python packages in `requirements.txt`: HTTP transport, graph search,
environment loading, and YAML parsing. Numerical acceleration, learned
retrieval, provider-specific tokenization, and native SMT bindings are optional
features and are not installed by default.

### Setup

Create the supported virtual environment and install the pinned dependencies:

```bash
./scripts/setup_venv.sh
```

Install Lean and Lake separately using the official
[Lean installation guide](https://lean-lang.org/install/), following the
`lean-toolchain` pin in the theorem project you intend to verify. The release
does not ship or provision Lean, Lake, Mathlib, PutnamBench, or downloaded
package trees.

For API providers, copy the environment template and add only the keys you use:

```bash
cp .env.example .env
```

`.env` is ignored by Git. Never commit provider credentials or generated run
artifacts.

## Run the prover

The live CLI help is authoritative:

```bash
.venv/bin/python -m ensemble_prover.mini_prover --help
```

For a Lean file or a directory containing Lean problems:

```bash
.venv/bin/python -m ensemble_prover.mini_prover /path/to/problems --prover openai
```

`--input /path/to/problems` and `--lean-file /path/to/problems` also work.
Mini finds unfinished theorem and lemma declarations, checks their inputs with
Lean, and runs them sequentially through the ordinary proof workflow. It infers
each source's containing Lake project; loose files use an available `lean_project`
runtime. Use `--project-path` to choose a different compatible project.
Add `--check-input` to perform only local preparation, without provider calls.
All model, reasoning, search, and budget options apply to each proof attempt.

For one named theorem in an arbitrary Lean project:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --lean-file /path/to/Target.lean \
  --theorem-name MyNamespace.target \
  --project-path /path/to/lake-project \
  --import Mathlib \
  --prover openai
```

Use `--supporting-source-dir` repeatedly when the theorem depends on source
trees outside the target file. `--description` or `--description-file` can add
mathematical context without changing the Lean contract.

For a PutnamBench source file:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --putnam-file external/PutnamBench/lean4/src/putnam_2025_a1.lean \
  --prover openai
```

The Putnam adapter expects a separately supplied compatible PutnamBench
checkout; no benchmark data or setup environment is bundled.

To use a ChatGPT Codex subscription for the prover or refiner, select
`--prover codex --prover-model <model>` and/or
`--refiner codex --refiner-model <model>` after `codex login`.
Set `--cost-budget-usd 0`; subscription usage is not priced as API usage.
See [Codex subscription setup and transport limits](CODEX_SUBSCRIPTION_BACKEND.md).

Claude Code subscription roles are also available with `--prover claude-code`
and/or `--refiner claude-code`, an explicit model such as `--prover-model opus`,
and `--cost-budget-usd 0`. See
[Claude Code setup and transport limits](CLAUDE_CODE_SUBSCRIPTION_BACKEND.md).

To sweep all locally unsolved PutnamBench problems in random order:

```bash
./scripts/sweep_putnam_unsolved.sh \
  --putnam-dir /path/to/PutnamBench/lean4/src \
  -- --prover openai --parallel-samples 2
```

Each attempt must commit one distinct accepted proof by 1,200 seconds and two by
1,800 seconds, both measured from proof worker readiness. Preparation and startup
have a separate 1,200-second cap. After two timely acceptances, normal
budgets apply. See the [sweep guide](../ensemble_prover/PUTNAM_SWEEP.md) for a
no-provider-call preview, resume commands, and counting/cleanup rules.

## Start from natural language

<details>
<summary>Translate one claim or develop a multi-file formalization campaign</summary>

For one claim, translate and prove using the OpenAI API:

```bash
.venv/bin/python -m ensemble_prover.nl_input \
  --text 'For every natural number n, n + 0 = n.' \
  --project-path /path/to/lake-project \
  --formalizer openai --formalizer-model gpt-5.6-terra \
  -- --prover openai --prover-model gpt-5.6-luna
```

Use `--text-file my_claim.md` for a UTF-8 document. To inspect the generated
statement without proof search, replace the final `-- --prover ...` line with
`--formalize-only`; a successful translation is not a proved theorem.

For longer notes requiring definitions and supporting lemmas, initialize a
resumable campaign:

```bash
.venv/bin/python -m ensemble_prover.formalization init \
  --project-path /path/to/lake-project \
  --source examples/formalization/finite_differences.md \
  --goal 'Formalize and prove the complete theorem in the supplied document.' \
  --output runs/formalization/my_project

.venv/bin/python -m ensemble_prover.formalization run runs/formalization/my_project \
  --max-steps 20 --max-model-calls 60

.venv/bin/python -m ensemble_prover.formalization status runs/formalization/my_project
```

Supply your own built Lean/Lake project with Mathlib and set `OPENAI_API_KEY`.
Campaign formalization and independent review default to `gpt-5.6-terra`;
proof search defaults to `gpt-5.6-luna`, all through OpenAI API name routing.
Repeat `run` to resume. Check for `status: proved` before exporting; exit 0
can also mean a resumable budget pause. Step/request budgets are not dollar
caps, and `--max-model-calls` excludes nested Mini proof-search calls and retries.

Inputs can be plain text, Markdown, LaTeX source, or papers already converted
to UTF-8 text. PDF/OCR extraction and URL downloading are not included. See
the [campaign walkthrough](USER_GUIDE.md#19-run-a-multi-file-formalization-campaign)
for review, revision, budgets, trust boundaries, and export commands.

These modules support long mathematical developments, but autonomous frontier
success rates and FLT/million-line performance have not been established.
Lean verification certifies the formal proof, not the accuracy of translation
from natural language. Review the generated definitions and statements.

</details>

## Investigate a mathematical problem

<details>
<summary>Initialize, run, and resume autonomous research</summary>

For human- or externally coordinated work, the [research ledger
guide](../ensemble_prover/research_claims/README.md) walks through recording claims,
arguments, reviews, quantitative requirements, and bounded assignments. The
ledger organizes work; its manual commands do not launch model workers.

For autonomous investigations, supply a complete UTF-8 problem file. No proof
sketch or choice of an affirmative conclusion is required. Add your existing,
built Lean/Lake project to enable the full research-to-proof loop. The default
transport is the OpenAI API; choose model names available to your account:

```bash
# Offline: save the problem and the limits for this research run.
.venv/bin/python -m ensemble_prover.research_claims discovery init runs/research/example \
  --problem problem.md \
  --project-path /path/to/built-lake-project \
  --model gpt-5.6-sol --review-model gpt-6-astra \
  --max-requests 32 --max-seconds 3600 --concurrency 4

# Paid: requires OPENAI_API_KEY; repeat this command to resume.
.venv/bin/python -m ensemble_prover.research_claims discovery run runs/research/example

.venv/bin/python -m ensemble_prover.research_claims discovery status runs/research/example
```

One `discovery run` drives research, formalization, independent statement review,
Mini proof search, checked export, and feedback. The request budget includes all
those roles, nested Mini dispatches, transport retries, and resumed requests.
The wall-clock limit starts at first execution and includes downtime; resuming
does not reset either limit. These are not dollar caps. Omit `--project-path` for
research-only execution. Add `--source notes.md` for supporting text,
`--import Mathlib` for a trusted project import, or `--experiments` for isolated,
bounded Python computations; `--import` requires a project.

For Codex subscription research, run `codex login` using ChatGPT, then add
`--provider codex` at initialization and choose Codex model names. This selects
Codex for research, formalization, proof search, refinement, and both argument
and semantic review, without an API key or API fallback. `--model` selects the
research/formalizer/prover/refiner model; `--review-model` selects both reviewers.
`--review-provider openai` explicitly selects API reviewers instead; the
reverse combination is also supported. One budgeted Codex dispatch is one
`codex exec` invocation, not each internal HTTP request. See
[Codex research setup](CODEX_SUBSCRIPTION_BACKEND.md#autonomous-research).

Workers can wait without model calls and resume when child findings arrive.
Full arguments, feedback, raw responses, and proof plans remain available as
artifacts. Recovery uses bounded working context with exact artifact and page
retrieval; workers must retrieve omitted content before judging it. The Codex
runtime may also manage context internally; exact underlying-model delivery
cannot be attested by this adapter. A reviewed proof or counterexample automatically
queues formalization when a project was configured. Proof work returns feedback
after at most `--proof-quantum-s 600` seconds or `--formalization-steps 8` controller
steps by default; `--lean-timeout-s` defaults to 300 seconds. A worker can continue
the same campaign or submit a revised complete plan for a fresh reviewed campaign.

`supported` means a written argument passed model review. Only an independently
rechecked export can set discovery `root_proved` or `root_refuted`; the latter
requires a formal proof of the original proposition's negation. Natural-language
alignment remains `machine_reviewed_not_certified`. An `idle` run or exit code 0
is not a mathematical success verdict.

Research-only runs can still save an exact handoff for separately authorized
standalone formalization; that separate command's requests are outside the
research cap. New ledgers use schema 7; schemas 1–6 require an explicit upgrade.
Migration preserves providers, budgets, and saved schema-6 closed-loop settings;
it does not authorize strategy recovery on existing ledgers.
There is no established autonomous discovery success rate. Recovery workers can
search Crossref metadata, fetch public primary sources, and inspect original PDF pages;
these tools do not provide comprehensive literature coverage.
See the [research
walkthrough](USER_GUIDE.md#21-run-autonomous-mathematical-research) and
[full execution contract](../ensemble_prover/research_claims/DISCOVERY.md).

</details>

## Start research from a saved run

From the repository directory, use one command:

```bash
./research runs/mini_prover/YOUR_RUN
```

This creates and starts integrated research, independent reviews and Lean proof
search using the saved Mini model, provider and project. It prints the new research
directory. New runs default to 4 hours and 200 model calls across all roles;
use `--hours 8 --requests 600` to choose a larger initial budget.

Pass the printed research directory to the same command to resume. Add `--status`
to inspect progress. Resuming preserves the original budget. Add `--prepare` when
creating a run to save it without starting model work, or `--source finding.txt`
to include an outside finding. Saved Codex and OpenAI providers are supported;
other providers require an explicit supported selection.

## Verify a checkout

Verify the installed Python environment and CLI:

```bash
.venv/bin/python -m pip check
.venv/bin/python -m ensemble_prover.mini_prover --help
.venv/bin/python -m ensemble_prover.nl_input --help
.venv/bin/python -m ensemble_prover.formalization --help
.venv/bin/python -m ensemble_prover.research_claims --help
.venv/bin/python -m ensemble_prover.research_claims discovery --help
```

Verify that the user-supplied target project can resolve its own toolchain:

```bash
(cd /path/to/lake-project && lake env lean --version)
```

## Output and local state

By default, runs are written beneath `runs/mini_prover/`. A run may contain a
human-readable log, structured turn records, activation telemetry, proof
artifacts, and a final summary. Generated runs, caches, local environments, and
secrets are excluded by `.gitignore`.

Research state lives in the directory supplied to the research CLI, including
`ledger.sqlite3` and content-addressed artifacts. Keep these records private
when the underlying mathematics is private; they include complete source text
and model conversations.

Persistent Mini theory defaults to `~/.cache/mini_prover/theory`. Use
`--mini-theory-root` to isolate experiments, `--mini-theory-mode read` for
retrieval-only operation, or `--mini-theory-mode off` to disable it.

Mathematical memory defaults to off. Add `--mathematical-memory observe` to
record existing outcomes or `--mathematical-memory assist` for bounded prior
theorem applications. Set `--mathematical-memory-root /path/to/catalog` to
isolate a campaign and `--mathematical-memory-seconds 90` for its action
allocation inside the run's existing governor. Developing generalizations
requires `--mathematical-memory develop --mini-theory-mode build` with a positive
`--mathematical-memory-research-seconds` allocation that does not exceed the
total memory action allocation (90 seconds by default). Reports and rankings cannot
replace ordinary proof acceptance. The default catalog root is
`~/.local/share/ensemble-prover/mathematical-memory`.
