# Codex subscription backend

Last updated: 2026-09-10.

Mini and autonomous discovery can use your saved **ChatGPT Codex subscription
sign-in** for their model roles. Select `codex` as the provider and explicitly select a model
available to your Codex account. API providers remain available independently.

## Setup and launch

Install a recent Codex CLI, then sign in interactively with ChatGPT:

```bash
codex login
codex login status
```

The status must say `Logged in using ChatGPT`. API-key authentication is rejected
by this backend. The CLI owns storage and refresh of the credentials. The prover
does not read or copy authentication files. A custom `CODEX_HOME` is respected.

Add these role options to your usual Mini command. Replace `YOUR_CODEX_MODEL`
with a model identifier available to your account; the roles may use different
models:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --lean-file /path/to/Target.lean \
  --theorem-name MyNamespace.target \
  --project-path /path/to/lake-project \
  --prover codex --prover-model YOUR_CODEX_MODEL \
  --refiner codex --refiner-model YOUR_CODEX_MODEL \
  --reasoning-effort high \
  --planner-escalation off \
  --cost-budget-usd 0
```

`--codex-bin /path/to/codex` selects an executable. Startup checks its flags,
version and sign-in without making a model request. Versions without
`--ignore-user-config`, `--ephemeral`, `--json` and `--output-schema` fail startup
checks.

An API-backed prover and a Codex refiner (or the reverse) are supported. If either
role uses Codex, automatic planner escalation is disabled so an API key elsewhere
in the environment cannot silently activate an API-billed planner. Explicit
planner provider selections retain their usual behavior.

This backend applies to Mini's prover/refiner and every model role in discovery's
integrated research-to-proof loop. The standalone `nl_input` and `formalization`
CLIs retain their API-backed model settings; the discovery loop injects its saved
clients into the formalization core. Claude Code is supported by Mini only.

## Autonomous research

After signing in with ChatGPT, supply a complete UTF-8 problem and an existing,
built Lean/Lake project. Replace the project path and model placeholders:

```bash
.venv/bin/python -m ensemble_prover.research_claims discovery init runs/research/codex_example \
  --problem problem.md --provider codex \
  --project-path /path/to/built-lake-project \
  --model YOUR_CODEX_MODEL --review-model YOUR_CODEX_REVIEW_MODEL \
  --max-requests 32 --max-seconds 3600 --concurrency 4

.venv/bin/python -m ensemble_prover.research_claims discovery run runs/research/codex_example
.venv/bin/python -m ensemble_prover.research_claims discovery status runs/research/codex_example
```

Initialization makes no model calls; `run` consumes subscription allowance and
drives research, formalization, Mini proof search, verified export, and feedback.
Omit `--project-path` for standalone research without automatic proof work.
Optional `--import Mathlib` selects a trusted project import and requires a project.

| Saved options | Roles selected |
| --- | --- |
| `--provider` and `--model` | Research worker, formalizer, Mini prover and refiner |
| `--review-provider` and `--review-model` | Argument reviewer and semantic statement reviewer |

`--review-provider` inherits `--provider`, so every role uses Codex in this
example. `--review-provider openai` explicitly selects API reviewers;
`--provider openai --review-provider codex` selects the reverse. API credentials
are needed only for API roles. There is no automatic API fallback. A custom
`--codex-bin` is saved with the run; relative
executable paths are anchored at initialization so a changed working directory
does not change their meaning on resume.

The request cap counts one `codex exec` invocation per subscription dispatch;
internal CLI HTTP retries are not individually observable. Research, both kinds
of review, formalization, and nested Mini dispatches share this cap and the
original wall-clock deadline, including downtime and resumes.
Neither cap is a dollar limit. Sign-in, usage-limit, and transport failures
preserve research state. Correct the problem, then repeat `discovery run` if
authorization remains. No allowance is automatically refunded or extended.

Workers and reviewers use separate clients and fresh ephemeral invocations.
Complete arguments pass through the same ledger and review gates as API-backed
research. The exact source and original proof plan remain required downstream
context; full diagnostics return to the investigator. The host does not trim
required content, but Codex can manage context internally as described below.
Reviewed proofs/counterexamples automatically queue proof work when the project
is configured. Defaults are `--proof-quantum-s 600`, `--formalization-steps 8`, and
`--lean-timeout-s 300`. A paused campaign retains its reviewed contracts, completed
modules, and pending source; an interrupted inner Mini invocation may restart
under the same global budget. Bounded local finalization can recover an already
saved proof after provider authorization is exhausted, without new model calls.

Research support/refutation is a review assessment. Only an independently
rechecked export sets discovery `root_proved` or `root_refuted`; a refutation
proves the original claim's logical negation. Natural-language alignment remains
`machine_reviewed_not_certified`. Manual `kernel_report` evidence cannot create
that authority. A research-only run can still save a handoff for separately
authorized standalone API formalization outside its research cap. Full instructions
are in
[User Guide section 21](USER_GUIDE.md#21-run-autonomous-mathematical-research).

New ledgers use schema 6. Stop older clients, back up version 1–5 ledgers, and run
`python -m ensemble_prover.research_claims upgrade DIRECTORY` explicitly before
opening them with this version. The upgrade preserves providers and budgets,
adds explicit API routing where required by old API-only formats, and leaves
automatic proving disabled. Missing routing or closed-loop authorization fields
in new-format runs are errors. Create a new discovery run with `--project-path`
to authorize the integrated workflow.

## Request and tool behavior

`CodexSubscriptionClient` implements `chat`, `chat_raw`, `chat_with_tools`,
`chat_n`, usage reporting and shutdown. Each request runs a fresh, ephemeral
`codex exec` in a temporary directory. Mini serializes its conversation and host
tool definitions into the request. Codex returns a schema-constrained envelope
containing text and/or tool requests, which the adapter validates and converts
to the existing function-call format.

The prover executes those tool requests, admits Lean artifacts and owns the
checkpoint. Resuming a checkpoint supplies its transcript to a fresh Codex
invocation; there is no hidden Codex thread that must be recovered. This is an
adapter around the Codex runtime, not a raw model endpoint or native API function
calling. Tool argument schemas are supplied in the prompt; function names and
JSON-object arguments are checked before returning them to Mini.

Invocations use ChatGPT-only authentication, the OpenAI provider, a read-only
sandbox, no interactive approvals, and an isolated working directory. User
configuration is ignored. Native shell, code execution, browsing, connectors,
plugins, hooks, delegation and shell snapshots are disabled. Host skill discovery
and skill instruction injection are disabled. Unexpected native action items
are rejected on every item lifecycle event. Codex can still expose built-in
utilities, including an apply-patch capability on some models; the read-only
sandbox is the write boundary. Event rejection is detection, not proof that no
native action ran. Prover tool requests are executed by Mini.

The host verifies that its serialized request retains required context. Codex may
manage or compact context internally; this adapter cannot attest that every
serialized token reaches the underlying model unchanged. Each invocation uses
the CLI's saved authentication store. Concurrent roles can refresh that store;
cross-process refresh coordination is owned by the CLI, not this adapter.
Inherited Codex endpoint overrides are removed, preserving only `CODEX_HOME`
and the CLI's sandbox context markers.

## Controls and accounting

- `--reasoning-effort low|medium|high|max` is supported (`max` maps to Codex's
  `xhigh`). Support for a chosen effort also depends on the selected model.
  Explicit reasoning-off is rejected by this transport.
- Temperature and top-p are not exposed by this CLI interface. Requested
  temperature is recorded as unsent. Parallel samples still make independent
  requests, but temperature variation does not apply.
- Output-token settings are **prompt targets**, not server-enforced caps. This
  distinction and the CLI version are published in request metadata.
- CLI turn usage reports input, cached-input, output and available reasoning
  tokens. These are recorded as unpriced subscription usage. A numeric zero
  subtotal is not a claim of zero cost or unlimited access.
- `--cost-budget-usd` must be zero when a Codex role is active. Subscription
  allowances cannot be valued or enforced using API per-token prices.
- One dispatch means one `codex exec` invocation. Codex may reconnect internally;
  its underlying HTTP requests are not individually observable by Mini.
- Existing request timeouts and hard deadlines cover admission, process startup
  and each invocation. `chat_n` shares one operation deadline across samples.
  Cancellation and shutdown kill and reap local process groups. Terminating a
  local process does not guarantee an already submitted remote generation stopped
  immediately.
- Subscription usage-limit and sign-in failures stop with classified errors;
  context overflow also stops rather than retrying the same oversized transcript.
  Transient transport failures use Mini's existing retry policy. Raw CLI stderr
  and authentication material are not copied into run artifacts.

Official references: [non-interactive Codex](https://learn.chatgpt.com/docs/non-interactive-mode),
[configuration](https://learn.chatgpt.com/docs/config-file/config-reference),
and [authentication](https://learn.chatgpt.com/docs/auth).
