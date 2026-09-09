# Codex subscription backend

Mini can use your saved **ChatGPT Codex subscription sign-in** for its prover
and refiner roles. Select `codex` as the provider and explicitly select a model
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

This backend applies to Mini's prover and refiner roles. The natural-language
frontends' formalizer and campaign model settings remain API-backed.

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

Mini verifies that its serialized request retains required context. Codex may
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
