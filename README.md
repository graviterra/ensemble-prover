# Ensemble Prover

Last updated: 2026-09-11.

This repository contains a research-grade autonomous theorem prover that
combines language-model proof search with Lean verification. Given a formalized
Lean target, it plans a proof, retrieves relevant declarations, decomposes hard
goals into helper claims, tests and repairs candidate proofs, and finalizes a
Lean-checked result without further user interaction. The maintained entry
point for proof search is `ensemble_prover.mini_prover`.

## Recent updates

September 2026 — highlights from the current source checkout:

- **Unknown-answer questions — experimental:** Mini can propose and review
  explicit terms for `answer(sorry)` slots, then try to prove the exact filled
  theorem. The original question is preserved; a proposed answer is not a proof.
  [Answer discovery](docs/USER_GUIDE.md#questions-with-an-unknown-answer)
- **Codex and Claude Code integration:** use subscription-backed CLI transports
  for Mini's prover and refiner, alongside the existing API providers. Codex
  also supports every model role in the research-to-proof loop.
  [Codex setup](docs/CODEX_SUBSCRIPTION_BACKEND.md) ·
  [Claude Code setup](docs/CLAUDE_CODE_SUBSCRIPTION_BACKEND.md)
- **Autonomous mathematical research — experimental:** explore proofs,
  counterexamples, and alternative approaches with model workers, fresh reviews,
  optional isolated experiments, and resumable request/time budgets. Supply a
  built Lake project to include formalization, Mini proof search, checked export,
  and feedback to research in the same run.
  [Start a research run](docs/USER_GUIDE.md#21-run-autonomous-mathematical-research)
- **Coordinated research:** track exact claims, full arguments, review objections,
  remaining gaps, and whether a helper actually advances the target problem.
  [Use the research ledger](docs/USER_GUIDE.md#20-coordinate-mathematical-research)
- **Natural-language formalization:** start from a single claim or longer notes,
  develop supporting Lean definitions and lemmas, and resume multi-file work.
  [Single claims](docs/USER_GUIDE.md#18-formalize-one-natural-language-claim) ·
  [Formalization campaigns](docs/USER_GUIDE.md#19-run-a-multi-file-formalization-campaign)

Research reviews are not Lean proof certificates. Autonomous research and its
integrated formalization/proof roles support the OpenAI API and Codex subscriptions.
The standalone NL and formalization CLIs remain API-backed. Claude Code integration
applies to Mini's prover/refiner roles. Older release snapshots may not include
every feature above.

## Overview

The primary input is a theorem, lemma, or conjecture in a user-supplied Lean
file and Lake project. PutnamBench files are supported through a compatibility
adapter, and callers may attach a natural-language problem description as
additional model context. Release 1.09 also includes
experimental natural-language entry points: `ensemble_prover.nl_input` for a
single claim and `ensemble_prover.formalization` for resumable, multi-file
projects. These translate text before proving; the resulting Lean statement
and its project environment remain the authoritative proof contract, not a
certificate of translation fidelity. Programmatic callers can submit the same generic
theorem-project request used by the CLI.

The current source checkout also includes experimental **mathematical research**
workflows. `ensemble_prover.research_claims` records exact claims, complete
arguments, independent reviews, remaining gaps, and whether a helper actually
advances its parent problem. Its `discovery` command runs autonomous
investigations: workers explore alternative approaches, seek proofs or
counterexamples, share findings, and request fresh reviews within a durable
request and time budget. Research can begin with a natural-language problem.
With a built Lake project, the same run formalizes candidate arguments, searches
for proofs, independently checks exports, and returns failures or results to
research. Omitting the project keeps a standalone research-only run.

As of August 2026, across research and evaluation runs, the system has produced
Lean-verified proofs for **65 distinct Putnam problems**, counting repeated
solves and configuration variants once. **PutnamBench has accepted all 65
submitted proofs**, and Ensemble Prover is listed on the
[PutnamBench leaderboard](https://trishullab.github.io/PutnamBench/leaderboard.html).
This is a cumulative demonstrated
result, not a claim of a controlled benchmark solve rate under one fixed model,
configuration, or budget. The prover has been tested with **GPT-5.2**,
**GPT-5.6 Luna-Pro**, **DeepSeek-V4-Flash**, **DeepSeek-V4-Pro**, and
**Qwen3.7-Max**. Prover, refiner, and planner-escalation roles are independently
configurable, so a run may use one model throughout or combine models.

Ensemble Prover is an actively developed research-grade tool. It continues to
solve Putnam problems and is now attempting frontier-mathematics problems.
The 65 accepted proofs are a snapshot of this ongoing work.

Every result reported as a solved proof by Mini Prover is checked by Lean.
Research-ledger support is a separate assessment, not a proved theorem.
Model responses, plans, retrieved material, speculative helper claims, and
falsification results are treated as
search evidence rather than proofs until they pass the relevant verification
gates. Each run records a structured, replayable dossier containing the proof
search and verification history.

## Putnam proofs accepted by PutnamBench

The following **65 problem identifiers** make up the cumulative result reported
above. Their Lean proof files were submitted privately to the PutnamBench
verification team for independent review on August 31, 2026; PutnamBench has
since accepted all 65 proofs. Only the problem identifiers are published here;
the proof files and answers are not.

| Period | Problems |
| --- | --- |
| 1960s | `1962 A6`, `1963 B1`, `1964 B1`, `1964 B2`, `1965 A4`, `1965 A6`, `1966 A1`, `1968 A1`, `1968 B2`, `1969 A1` |
| 1970s | `1970 B3`, `1971 A1`, `1971 B1`, `1972 A1`, `1972 A2`, `1973 B2`, `1975 B1`, `1977 A2`, `1977 A3`, `1977 A5`, `1978 A1`, `1978 A4`, `1979 B6` |
| 1980s | `1986 A1`, `1986 B1`, `1986 B6`, `1987 A1`, `1987 A2`, `1988 B1`, `1988 B2` |
| 1990s | `1990 A1`, `1990 A5`, `1990 A6`, `1991 A2`, `1992 A1`, `1992 A2`, `1993 A2`, `1995 A1`, `1996 A3`, `1997 A4`, `1998 B1`, `1998 B2`, `1999 A1` |
| 2000s | `2000 A1`, `2000 B2`, `2001 A1`, `2003 B1`, `2004 A1`, `2004 B2`, `2005 A1`, `2005 B1`, `2006 A1`, `2007 B1`, `2008 A1`, `2009 A1` |
| 2010s | `2010 A2`, `2012 A2`, `2016 A1` |
| 2020s | `2021 A1`, `2021 A2`, `2024 A1`, `2024 B3`, `2025 A1`, `2025 B2`, `2025 B3` |

> **Release status:** 1.09 — research preview. Includes Mini Prover, experimental
> single-claim NL input, and resumable multi-file formalization campaigns.
> Optional Codex and Claude Code subscription backends serve Mini's prover and refiner,
> alongside the existing API providers. Codex also serves autonomous research.
> The current source also includes experimental coordinated and autonomous
> research; older release snapshots may not contain these entry points.

## Documentation

Start with the **[User Guide](docs/USER_GUIDE.md)** for installation, theorem
project preparation, [single-claim NL input](docs/USER_GUIDE.md#18-formalize-one-natural-language-claim),
[long formalization projects](docs/USER_GUIDE.md#19-run-a-multi-file-formalization-campaign),
[coordinated research](docs/USER_GUIDE.md#20-coordinate-mathematical-research),
[autonomous research](docs/USER_GUIDE.md#21-run-autonomous-mathematical-research),
provider configuration, budgets, outputs, proof graphs, diagnostic replay,
troubleshooting, and the public Mini CLI option map.

## Highlights

- Autonomous Lean-checked proof search
- Recursive helper planning and root-proof assembly
- Deterministic tactic, retrieval, and falsification lanes
- Provider-call, wall-clock, and cost-budget controls
- Persistent verified Mini theory and proof-state caches
- Structured JSONL traces, summaries, and replay tooling
- Natural-language/LaTeX-text translation with explicit Lean proof contracts
- Resumable multi-file development with independent model review and checked exports
- Complete required plan/context delivery, with explicit errors when model limits are exceeded
- Research claims with separate correctness, verification, and contribution assessments
- Autonomous research programs with fresh reviews, durable feedback, and fair research scheduling
- Optional isolated Python experiments and complete research-to-formalization handoffs

## Requirements

- Linux
- Standard CPython 3.11 or 3.12 (release audited on both)
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
features and are not installed by default. The development worktree may retain
a broader research environment than the public snapshot.

## Setup

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

For an arbitrary Lean theorem project:

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
See [Codex subscription setup and transport limits](docs/CODEX_SUBSCRIPTION_BACKEND.md).

Claude Code subscription roles are also available with `--prover claude-code`
and/or `--refiner claude-code`, an explicit model such as `--prover-model opus`,
and `--cost-budget-usd 0`. See
[Claude Code setup and transport limits](docs/CLAUDE_CODE_SUBSCRIPTION_BACKEND.md).

To sweep all locally unsolved PutnamBench problems in random order:

```bash
./scripts/sweep_putnam_unsolved.sh \
  --putnam-dir /path/to/PutnamBench/lean4/src \
  -- --prover openai --parallel-samples 2
```

Each attempt must commit one distinct accepted proof by 600 seconds and two by
1,800 seconds, both measured from launch. After two timely acceptances, normal
budgets apply. See the [sweep guide](ensemble_prover/PUTNAM_SWEEP.md) for a
no-provider-call preview, resume commands, and counting/cleanup rules.

## Start from natural language

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
the [campaign walkthrough](docs/USER_GUIDE.md#19-run-a-multi-file-formalization-campaign)
for review, revision, budgets, trust boundaries, and export commands.

These modules support long mathematical developments, but autonomous frontier
success rates and FLT/million-line performance have not been established.
Lean verification certifies the formal proof, not the accuracy of translation
from natural language. Review the generated definitions and statements.

## Investigate a mathematical problem

For human- or externally coordinated work, the [research ledger
guide](ensemble_prover/research_claims/README.md) walks through recording claims,
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
[Codex research setup](docs/CODEX_SUBSCRIPTION_BACKEND.md#autonomous-research).

Workers can wait without model calls and resume when child findings arrive.
Full arguments, feedback, raw responses, and proof plans remain available as
artifacts; the harness does not silently shorten required context. The Codex
runtime may manage context internally; exact underlying-model delivery cannot
be attested by this adapter. A reviewed proof or counterexample automatically
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
research cap. Schema 6 requires an explicit upgrade for version 1–5 ledgers and
preserves providers and budgets without enabling automatic proving on old runs.
Three offline scripted/fake-Codex trajectories have exercised real Lean checks;
they are integration tests, not a discovery-performance benchmark. There is no
automatic literature search or established autonomous discovery success rate.
See the [research
walkthrough](docs/USER_GUIDE.md#21-run-autonomous-mathematical-research) and
[full execution contract](ensemble_prover/research_claims/DISCOVERY.md).

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

## Security and trust boundary

Only Lean-accepted artifacts should be treated as proved. Language-model text,
planner receipts, speculative helpers, and falsification probes are search
evidence—not proofs—until independently checked against the target project.

Run the prover on untrusted theorem projects only inside an appropriately
isolated environment. The prover executes Lean and local subprocesses and may
send theorem context to configured external model providers. Provider keys and
common token, secret, password, private-key, cloud-identity, auth-config, and
credential-bearing URL variables are stripped from Lean, Lake, and other
local-tool child environments. Credential-bearing parent and watchdog
processes are also marked non-dumpable on Linux to block descendant `/proc`
inspection. Untrusted Lean code still runs with the prover user's filesystem
and network privileges, so operating-system isolation may still be required. A
Python virtual environment is not a security boundary.

## Contributing and licensing

See [SECURITY.md](SECURITY.md) for private vulnerability reporting.
This project is licensed under the MIT License. See [LICENSE](LICENSE).
