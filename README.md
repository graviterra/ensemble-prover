# Ensemble Prover

This repository contains a research-grade autonomous theorem prover that
combines language-model proof search with Lean verification. Given a formalized
Lean target, it plans a proof, retrieves relevant declarations, decomposes hard
goals into helper claims, tests and repairs candidate proofs, and finalizes a
Lean-checked result without further user interaction. The maintained entry
point is `ensemble_prover.mini_prover`.

The primary input is a theorem, lemma, or conjecture in a user-supplied Lean
file and Lake project. PutnamBench files are supported through a compatibility
adapter, and callers may attach a natural-language problem description as
additional model context. Natural language alone is not currently a proof
input: the Lean statement and its project environment remain the authoritative
contract. Programmatic callers can submit the same generic theorem-project
request used by the CLI.

As of August 2026, across research and evaluation runs, the system has produced
Lean-verified proofs for **65 distinct Putnam problems**, counting repeated
solves and configuration variants once. This is a cumulative demonstrated
result, not a claim of a controlled benchmark solve rate under one fixed model,
configuration, or budget. The prover has been tested with **GPT-5.2**,
**GPT-5.6 Luna-Pro**, **DeepSeek-V4-Flash**, **DeepSeek-V4-Pro**, and
**Qwen3.7-Max**. Prover, refiner, and planner-escalation roles are independently
configurable, so a run may use one model throughout or combine models.

Every accepted result is checked by Lean. Model responses, plans, retrieved
material, speculative helper claims, and falsification results are treated as
search evidence rather than proofs until they pass the relevant verification
gates. Each run records a structured, replayable dossier containing the proof
search and verification history.

> **Release status:** research preview. This release contains only the Mini
> Prover runtime.

## Highlights

- Autonomous Lean-checked proof search
- Recursive helper planning and root-proof assembly
- Deterministic tactic, retrieval, and falsification lanes
- Provider-call, wall-clock, and cost-budget controls
- Persistent verified Mini theory and proof-state caches
- Structured JSONL traces, summaries, and replay tooling

## Requirements

- Linux
- Standard CPython 3.11 (the verified release runtime)
- Lean toolchain compatible with the target Lake project
- An API key for the selected language-model provider

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

Install Lean and Lake separately, following the toolchain pin in the theorem
project you intend to verify. The release does not ship or provision Lean,
Lake, Mathlib, PutnamBench, or downloaded package trees.

Copy the environment template and add only the provider keys you use:

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

## Verify a checkout

Verify the installed Python environment and CLI:

```bash
.venv/bin/python -m pip check
.venv/bin/python -m ensemble_prover.mini_prover --help
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

Persistent Mini theory defaults to `~/.cache/mini_prover/theory`. Use
`--mini-theory-root` to isolate experiments, `--mini-theory-mode read` for
retrieval-only operation, or `--mini-theory-mode off` to disable it.

## Security and trust boundary

Only Lean-accepted artifacts should be treated as proved. Language-model text,
planner receipts, speculative helpers, and falsification probes are search
evidence—not proofs—until independently checked against the target project.

Run the prover on untrusted theorem projects only inside an appropriately
isolated environment. The prover executes Lean and local subprocesses and may
send theorem context to configured external model providers.

## Contributing and licensing

See [SECURITY.md](SECURITY.md) for private vulnerability reporting.
This project is licensed under the MIT License. See [LICENSE](LICENSE).
