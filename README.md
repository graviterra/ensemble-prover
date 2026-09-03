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

## Putnam problems submitted for independent verification

The following **65 problem identifiers** make up the cumulative result reported
above. Their Lean proof files were submitted privately to the PutnamBench
verification team for independent review on August 31, 2026. Submission does
not imply review, acceptance, or endorsement by PutnamBench. Only the problem
identifiers are published here; the proof files and answers are not.

| Period | Problems |
| --- | --- |
| 1960s | `1962 A6`, `1963 B1`, `1964 B1`, `1964 B2`, `1965 A4`, `1965 A6`, `1966 A1`, `1968 A1`, `1968 B2`, `1969 A1` |
| 1970s | `1970 B3`, `1971 A1`, `1971 B1`, `1972 A1`, `1972 A2`, `1973 B2`, `1975 B1`, `1977 A2`, `1977 A3`, `1977 A5`, `1978 A1`, `1978 A4`, `1979 B6` |
| 1980s | `1986 A1`, `1986 B1`, `1986 B6`, `1987 A1`, `1987 A2`, `1988 B1`, `1988 B2` |
| 1990s | `1990 A1`, `1990 A5`, `1990 A6`, `1991 A2`, `1992 A1`, `1992 A2`, `1993 A2`, `1995 A1`, `1996 A3`, `1997 A4`, `1998 B1`, `1998 B2`, `1999 A1` |
| 2000s | `2000 A1`, `2000 B2`, `2001 A1`, `2003 B1`, `2004 A1`, `2004 B2`, `2005 A1`, `2005 B1`, `2006 A1`, `2007 B1`, `2008 A1`, `2009 A1` |
| 2010s | `2010 A2`, `2012 A2`, `2016 A1` |
| 2020s | `2021 A1`, `2021 A2`, `2024 A1`, `2024 B3`, `2025 A1`, `2025 B2`, `2025 B3` |

> **Release status:** v1.0.3 — provider retry, scheduler recovery, and lane
> lease reliability hardening. v1.0.2 updated dependency security; v1.0.1
> added credential isolation and the user guide. Releases contain only the
> Mini Prover runtime.

## Documentation

Start with the **[User Guide](docs/USER_GUIDE.md)** for installation, theorem
project preparation, provider configuration, budgets, outputs, proof graphs,
diagnostic replay, troubleshooting, and the complete public CLI option map.

## Highlights

- Autonomous Lean-checked proof search
- Recursive helper planning and root-proof assembly
- Deterministic tactic, retrieval, and falsification lanes
- Provider-call, wall-clock, and cost-budget controls
- Persistent verified Mini theory and proof-state caches
- Structured JSONL traces, summaries, and replay tooling

## Requirements

- Linux
- Standard CPython 3.11 or 3.12 (release audited on 3.11)
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

Install Lean and Lake separately using the official
[Lean installation guide](https://lean-lang.org/install/), following the
`lean-toolchain` pin in the theorem project you intend to verify. The release
does not ship or provision Lean, Lake, Mathlib, PutnamBench, or downloaded
package trees.

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
