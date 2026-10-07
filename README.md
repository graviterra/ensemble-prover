<h1 align="center">Ensemble Prover</h1>

<p align="center"><strong>Language models search and propose.<br>Lean decides.</strong></p>

<p align="center">
  An open-source workspace for autonomous theorem proving and mathematical research.
</p>

<p align="center">
  <a href="#quick-start">Get started</a> ·
  <a href="#your-proof-workspace">Explore the UI</a> ·
  <a href="https://www.graviterra.org/ensemble-prover#proof">A real proof</a> ·
  <a href="#documentation">Documentation</a> ·
  <a href="https://www.graviterra.org/ensemble-prover">Website ↗</a>
</p>

Give it a Lean theorem, formalize a mathematical claim, or investigate an open
problem. Follow the approach, inspect the helpers, and take the Lean proof with
you. Ensemble Prover coordinates models, supporting lemmas, proof repair, and
research into alternative approaches in a local workspace.

[![Ensemble Prover proof graph with a selected helper, its Lean statement, and expanded proof source](docs/assets/ui-proof-inspector.png)](docs/assets/ui-proof-inspector.png)

<p align="center"><em>Follow the proof. Open the helpers. Inspect the Lean.</em></p>

| 672 Putnam problems | Lean 4 | Open source |
| :---: | :---: | :---: |
| [With saved solutions](#results) | Inspectable statements and proofs | MIT · Version 1.18 |

Cumulative across models · October 7, 2026 · Research preview

The screenshots show the actual interface with illustrative example records.
Click an image to view it at full size.

## Work with the mathematics

### Know what is blocking the proof

The **Mathematical focus** panel connects the active approach, its blocking
obligation, what the last expensive action established, and the scheduler's
recorded reason for choosing the next action. Open a helper to read its Lean
statement and available proof source.

[Explore proof search →](docs/proof-search.md)

### Give another approach room to develop

Adaptive frontier control keeps separate approaches and research questions in
play. It reserves exploration alongside work that advances the original theorem.
Research can investigate an obstruction, inspect sources, and bring findings
back into proof search.

[Configure adaptive research →](docs/USER_GUIDE.md#automatic-research-when-proof-search-stalls)

### Make a useful lemma useful again

Search mathematical declarations, test applications, and restore compatible
checked helpers. Optional mathematical memory records applicability, successful
uses, and failed applications. A failed attempt remains distinct from a proof
that a claim is false; generalized lemmas require their own Lean checks.

[Explore mathematical memory →](docs/mathematical-memory.md)

<a id="choose-a-workflow"></a>

## Bring the mathematics you have

| Start with | Use | Guide |
| --- | --- | --- |
| A Lean theorem | Browser or Mini CLI | [Theorem projects](docs/USER_GUIDE.md#4-prepare-an-arbitrary-theorem-project) |
| An English or LaTeX claim | Browser or natural-language CLI | [Single-claim formalization](docs/USER_GUIDE.md#18-formalize-one-natural-language-claim) |
| Longer mathematical notes | Formalization campaign CLI | [Multi-file developments](docs/USER_GUIDE.md#19-run-a-multi-file-formalization-campaign) |
| A problem to investigate | Autonomous research CLI | [Research and proof feedback](docs/USER_GUIDE.md#21-run-autonomous-mathematical-research) |
| An existing Mini run | `./research /path/to/run` | [Research from saved work](docs/CLI_QUICKSTART.md#start-research-from-a-saved-run) |
| A collection of PutnamBench problems | Sweep script | [Sequential sweeps](ensemble_prover/PUTNAM_SWEEP.md) |

Natural-language formalization and autonomous research are experimental.
Research arguments and translation results require further checking before
they can support a proof claim.

[Walk through a real Putnam proof →](https://www.graviterra.org/ensemble-prover#proof)
See how a local derivative estimate becomes a proof of the original theorem,
with the helper and final Lean proof available to inspect.

## Quick start

The browser workspace requires **Linux**, standard **CPython 3.11 or 3.12**, and
**Node.js 22.20+ (22.x), 24.12+ (24.x), or 26+** to build the page. Node is not
needed while serving the built UI.

```bash
git clone https://github.com/graviterra/ensemble-prover.git
cd ensemble-prover

python3.11 -m venv .venv
.venv/bin/python -m pip install -r requirements-interface.txt
.venv/bin/python -m pip check
npm --prefix interface/web ci
npm --prefix interface/web run build

.venv/bin/python -m interface.service --control
```

Open **[http://127.0.0.1:8765](http://127.0.0.1:8765)**. Use `python3.12` in the
virtual-environment command if preferred. Omit `--control` for read-only browsing.

To start proof work, supply a **compatible, built Lean/Lake project** and model
access. Install Lean and Lake using the [official guide](https://lean-lang.org/install/)
and your project's `lean-toolchain` pin. Lean, Mathlib, and benchmark datasets
are supplied separately.

<details>
<summary>Model access, local inference, and provider setup</summary>

For browser launches, export provider credentials in the service shell, or use
an existing supported subscription CLI sign-in. The service does not load `.env`.
Choose a formalizer separately for English-to-Lean translation; its default is
the OpenAI API. Mini supports API providers, Codex and Claude Code subscription
backends, and operator-configured local inference servers. Local deployments
use one adapter for generic compatible chat servers, vLLM, Ollama, and
llama.cpp. Register a profile with `ENSEMBLE_LOCAL_INFERENCE_CONFIG` to select
its deployments in the browser. A declared deployment is not a live
compatibility check. Cursor CLI generation currently remains unavailable and
is rejected before spawning the agent.

</details>

The workspace runs on localhost with trusted users, projects, and state
directories. Keep it local; it is not a shared network service.

[Browser setup and controls](interface/README.md) ·
[CLI quick start](docs/CLI_QUICKSTART.md) ·
[Codex setup](docs/CODEX_SUBSCRIPTION_BACKEND.md) ·
[Claude Code setup](docs/CLAUDE_CODE_SUBSCRIPTION_BACKEND.md) ·
[Local inference, budgets, and readiness](docs/local-inference.md) ·
[Provider and workflow compatibility](docs/providers.md)

<a id="local-browser-interface"></a>

## Your proof workspace

**Configure the attempt.** Start from English or LaTeX, or choose a Lean project,
file, and theorem. Select your prover and optional refiner, set search and budget
controls, and review the configuration before starting.

**Follow the mathematics.** Move between the mathematical focus, proof graph,
and timeline. Inspect the target and distinguish work on a helper from work on
the original theorem. Runtime details show the recorded source revision,
model and reasoning settings, output allowance, and infrastructure observations.

**Return to the work that matters.** Search saved attempts, filter by sweep or
outcome, and reopen their evidence. Results show process status and proof status
together. Closing the browser leaves an attempt running; owned attempts support
a confirmed cooperative stop.

<details>
<summary>See the launcher and results library</summary>

### Configure a run

[![Launcher with mathematical input, project selection, model settings, and launch guidance](docs/assets/ui-launcher.png)](docs/assets/ui-launcher.png)

### Explore saved work

[![Results library with searchable attempts, outcome filters, and separate proof and process statuses](docs/assets/ui-results.png)](docs/assets/ui-results.png)

The binomial-square export shown here uses a supplied proof checked by the
export verifier.

</details>

[Explore the browser interface →](interface/README.md)

## How it works

**Plan → Retrieve → Prove → Repair → Export**

Plans become scoped helper obligations. Retrieval brings supporting mathematics
into view. Models propose proofs; Lean checks them and supplies concrete feedback
for repair. Checked helpers return to work on the original theorem. Export
reconstructs the source, replays it in Lean, and audits the axioms it uses.

Choose the model for each role: hosted APIs, supported subscription CLIs, or
compatible inference servers on your hardware. Configure prover, refiner, and
planner roles independently. The workspace runs locally; selected providers
and enabled research tools can make external requests.

[Model roles and provider compatibility →](docs/providers.md)

<details>
<summary>Explore the subsystems and optional controls</summary>

| Capability | What it enables |
| --- | --- |
| **Recursive proof search** | Develop scoped helper lemmas, track route dependencies, and assemble a proof of the original theorem. |
| **Progress toward the root** | Prefer blocking obligations and ready assemblies while preserving opportunities for speculative mathematics. |
| **Lean feedback and formal search** | Repair candidates from concrete errors; optionally explore a persistent frontier of tactic states. |
| **Counterexample certification** | Investigate doubtful claims and require an audited Lean proof before treating a claim as refuted. |
| **Retrieval and reusable theory** | Find declarations, test applications, recheck cached helpers, and build compatible verified theory bundles. |
| **Mathematical memory** | Optionally record applicability, successful use, failed applications, and independently checked generalization work. |
| **Research and alternatives** | Investigate obstructions, inspect sources, sustain alternative approaches, and return findings to proof work under existing budgets. |
| **Formalization and answer discovery** | Translate claims, develop multi-file projects, or propose an explicit answer before proving the instantiated question. |
| **Model coordination** | Select prover, refiner, planner, and workflow-specific roles across API, subscription, and configured local inference transports. |
| **Persistent work** | Retain checkpoints, accounting, source provenance, and evidence for inspection and supported recovery. |
| **Verified exports** | Reconstruct source, replay it in Lean, audit axioms, and produce readable proofs and dependency graphs. |

English input first passes through formalization. Longer developments can use
resumable campaigns to build definitions and supporting theorems across files.
Autonomous research can investigate arguments and counterexamples before
handing candidates to formalization and proof search.

The search controls are independent. Recursive proving and automatic research
are enabled for new Mini runs; formal-state search, adaptive frontier allocation,
mathematical memory, and helper promotion require their own opt-ins. Memory's
portable application history additionally requires a trusted source-authority
integration; the standard CLI does not automatically transfer that history
between problems. [Explore the system and its defaults →](docs/proof-search.md)

</details>

**The proof certificate is a verified export.** A helper or internal solve is
progress toward it. Lean verifies the formal statement; review generated
statements and definitions to check that they express your intended mathematics.
The system supports work on open problems, but does not promise autonomous
solutions, complete literature coverage, or novelty certification.

<a id="run-the-prover"></a>

## Run from the terminal

Pass a Lean file or a directory of problems:

```bash
.venv/bin/python -m ensemble_prover.mini_prover /path/to/problems --prover openai
```

Mini discovers unfinished theorems recursively, infers each file's Lake project,
and starts supervised proof attempts. Loose files can use an available
`lean_project` runtime, or an explicit `--project-path`. Add `--check-input` to
verify preparation without model calls. Original source files remain unchanged.

To select a particular theorem in an existing project:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --lean-file /path/to/Target.lean \
  --theorem-name MyNamespace.target \
  --project-path /path/to/lake-project \
  --import Mathlib --prover openai
```

For a local server, replace the provider selection with a registered deployment:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --lean-file /path/to/Target.lean --theorem-name MyNamespace.target \
  --project-path /path/to/lake-project \
  --local-inference-config examples/local-inference.yaml \
  --prover local --prover-deployment math \
  --refiner local --refiner-deployment math --inference-policy local-only
```

Edit the [example profile](examples/local-inference.yaml) for the model actually
served. Local compute has its own finite dispatch, output, and request-time
budgets; zero marginal API cost does not mean unlimited compute. See the
[local inference guide](docs/local-inference.md) for browser registration,
bounded compatibility probes, and uncertain-completion recovery. `local-only`
selects inference locality; it does not make the whole application offline.

Use `--help` for the options in your checkout. For a CLI-only installation and
examples covering natural language, campaigns, research, and sweeps, see the
[CLI quick start](docs/CLI_QUICKSTART.md).

## Results

**672 distinct Putnam problems with saved solutions**, accumulated across models,
configurations, and budgets as of October 7, 2026.

This is a cumulative archive, not a controlled benchmark solve rate. Individual
artifacts retain their verification and axiom records. See the results guide
for problem identifiers, evaluation scope, and independent verification status.

[Results and evaluation scope →](docs/RESULTS.md) ·
[PutnamBench leaderboard](https://trishullab.github.io/PutnamBench/leaderboard.html)

Our Putnam evaluation uses the formalized problems provided by
[PutnamBench](https://github.com/trishullab/PutnamBench). We thank its authors
and contributors for making this benchmark available. See
[the paper](https://arxiv.org/abs/2407.11214).

## Documentation

[Documentation home: workflows, subsystems, and feature availability →](docs/README.md)

| Learn about | Start here |
| --- | --- |
| Browser installation, controls, storage, and limitations | [Interface guide](interface/README.md) |
| Terminal commands for proving, formalization, and research | [CLI quick start](docs/CLI_QUICKSTART.md) |
| Providers, project setup, search, and troubleshooting | [User Guide](docs/USER_GUIDE.md) |
| Complete LLM instructions, task templates, and source locations | [Prompt reference](docs/LLM_PROMPTS.md) |
| Model roles, hosted APIs, subscriptions, and local inference | [Providers](docs/providers.md) |
| Root blockers, recursive helpers, formal search, and refutation | [Proof search](docs/proof-search.md) |
| Retrieval, reusable theory, application history, and generalization | [Mathematical memory](docs/mathematical-memory.md) |
| Time, provider-call, and API cost controls | [Budgets](docs/USER_GUIDE.md#7-set-time-and-cost-boundaries) |
| Proof status, exports, and inspection | [Reading results](docs/USER_GUIDE.md#11-determine-whether-a-run-succeeded) · [Exports](docs/USER_GUIDE.md#12-standalone-exports-and-proof-graphs) |
| Checkpoints, interruption, and resumption | [Recovery guide](docs/USER_GUIDE.md#13-replay-and-interruption-behavior) |
| Monitoring, diagnosing slow work, and managing long runs | [Operations](docs/operations.md) |
| Research execution and formalization handoffs | [Research guide](ensemble_prover/research_claims/DISCOVERY.md) |
| Local execution, privacy, and vulnerability reporting | [Security](SECURITY.md) |

## Cite this work

> Reale, M. (2026). *Ensemble Prover* (Version 1.18) [Computer software]. Graviterra.

```bibtex
@software{reale2026ensembleprover,
  author       = {Reale, M.},
  title        = {{Ensemble Prover}},
  year         = {2026},
  version      = {1.18},
  organization = {Graviterra},
  url          = {https://github.com/graviterra/ensemble-prover}
}
```

Identify the version or commit used for reproducibility.
[CITATION.cff](CITATION.cff) provides machine-readable citation metadata.

Ensemble Prover is licensed under the MIT License. See [LICENSE](LICENSE).
