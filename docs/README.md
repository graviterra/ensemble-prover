# Ensemble Prover documentation

Ensemble Prover develops mathematical arguments, searches for Lean proofs, and
retains the evidence needed to inspect its work. Start with a formal theorem,
translate a claim, or investigate a problem before choosing a proof approach.

## Start here

| Your task | Guide |
| --- | --- |
| Install and launch the browser workspace | [Quick start](../README.md#quick-start) · [Interface guide](../interface/README.md) |
| Run a Lean theorem or directory of problems | [CLI quick start](CLI_QUICKSTART.md#run-the-prover) |
| Choose models, transports, and reasoning controls | [Providers and model roles](providers.md) |
| Read the complete LLM prompts and find their definitions | [Prompt reference](LLM_PROMPTS.md) |
| Understand how the prover chooses and checks work | [Proof search and mathematical research](proof-search.md) |
| Reuse lemmas and understand application history | [Retrieval, theory, and mathematical memory](mathematical-memory.md) |
| Monitor, stop, resume, or diagnose a run | [Operations and recovery](operations.md) |
| Find detailed command settings | [User Guide](USER_GUIDE.md) · each command's `--help` |

## Workflow map

| Input | Workflow | Output and completion boundary |
| --- | --- | --- |
| Lean source with unfinished proofs | Mini Prover | Search artifacts and, on success, a freshly checked proof export |
| A question containing an unknown answer | [Answer discovery](USER_GUIDE.md#questions-with-an-unknown-answer) | A reviewed candidate answer followed by proof search for that exact instantiated question |
| English or LaTeX claim | [Single-claim formalization](nl_input.md) | A typechecked statement; optionally a Mini proof attempt |
| Mathematical notes requiring new definitions and lemmas | [Formalization campaign](formalization-campaign.md) | Resumable multi-file development with independently reviewed statements and checked module admission |
| An open problem or a stalled proof strategy | [Autonomous research](../ensemble_prover/research_claims/DISCOVERY.md) | Arguments, reviewed evidence, alternative approaches, and optional formalization/proof feedback |
| Claims coordinated by a mathematician or external workers | [Research ledger](../ensemble_prover/research_claims/README.md) | Versioned claims, dependencies, artifacts, and reviews; no automatic proof authority |
| A PutnamBench collection | [Sequential sweeps](../ensemble_prover/PUTNAM_SWEEP.md) | Per-attempt results, saved acceptance deadlines, and resumable sweep state |

The browser launches individual Lean and natural-language attempts and follows
existing sweeps. Multi-file campaigns and open-ended research use their CLIs.

## Subsystem map

| Subsystem | What it does | Documentation |
| --- | --- | --- |
| Input preparation and project capture | Locates declarations, preserves the target context, checks environments, and prepares answer candidates | [Theorem projects](USER_GUIDE.md#4-prepare-an-arbitrary-theorem-project) |
| Prover, refiner, and planner | Generate candidates, repair failures, and propose scoped recursive work | [Roles](providers.md#roles-and-routing) |
| Proof graph, route contracts, and scheduling | Track obligations and prioritize blockers while retaining exploratory work | [Root progress](proof-search.md#progress-toward-the-original-theorem) |
| Recursive helpers and root assembly | Prove smaller obligations and attempt to compose them into the original theorem | [Search lanes](proof-search.md#the-search-lanes) |
| Lean verification and mathematical identity | Check terms, contexts, dependent binders, selected statement variants, and proof dependencies | [What Lean establishes](proof-search.md#what-lean-establishes) |
| Formal-state search | Explore and resume a bounded frontier of Lean tactic states | [Formal-state search](proof-search.md#formal-state-search) |
| Falsification and counterexample certification | Distinguish exploratory observations from an audited proof of negation | [Refutation](proof-search.md#counterexamples-and-failed-approaches) |
| Mathematical retrieval and model tools | Search declarations, inspect types, probe applications, and compute examples | [Retrieval layers](mathematical-memory.md#four-different-kinds-of-reuse) |
| Verified-helper cache and Mini theory | Recheck saved helpers and publish compatible reusable bundles | [Persistent theory](mathematical-memory.md#mini-theory-and-helper-promotion) |
| Mathematical memory | Record applicability, use, failed applications, and checked generalization work | [Memory modes](mathematical-memory.md#memory-modes) |
| Research recovery and frontier control | Investigate obstructions, sustain alternatives, inspect literature, and feed results back into proof work | [Research policies](proof-search.md#research-and-alternative-approaches) |
| Provider adapters and local compute coordinator | Route requests, validate responses, and account for shared local inference capacity | [Providers](providers.md) · [Local inference](local-inference.md) |
| Run governor and checkpoint ledger | Bound work, retain durable state, and recover within saved authorization | [Budgets and recovery](operations.md) |
| Export, axiom audit, and proof presentation | Reconstruct and recheck source, simplify presentation conservatively, and generate dependency graphs | [Proof exports](USER_GUIDE.md#12-standalone-exports-and-proof-graphs) |
| Browser workspace and run telemetry | Show mathematical focus, Lean source, runtime settings, memory, results, and cooperative controls | [Interface](../interface/README.md) |

## Reading claims about success

A retrieved lemma is a candidate. A successful application probe may still leave
obligations. A checked helper proves its own statement. An internal root proof
still needs export verification. Use the verified export and its recorded target,
environment, and axiom audit when reporting a formal result.

Lean checks the formal proposition. It does not certify that a translation
captures the intended English mathematics, that a result is novel, or that a
research route will succeed. Scheduling priorities and model reviews cannot
substitute for a proof.

[Results and evaluation scope](RESULTS.md) · [Security and privacy](../SECURITY.md)

## Scope and defaults

These guides describe version 1.18. Features with separate opt-ins include
formal-state search, adaptive frontier research, mathematical memory, helper
promotion, and browser control. Their settings are independent; enabling one
does not silently enable the others. See the
[default behavior table](proof-search.md#defaults-and-opt-ins).

Examples use a separately installed, built Lean/Lake project. Model identifiers
are provider-specific; select models available to your account or local server.
The release does not include model weights, benchmark answers, or the Lean and
Mathlib dependency trees.
