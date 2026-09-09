# Claude Code subscription backend

Mini can use your saved Claude.ai subscription login for the prover and refiner
roles through the installed Claude Code CLI. Select provider `claude-code` and
an explicit model available to your account. The transport runs the official
`claude -p` interface; it does not extract tokens or call private endpoints.

## Setup and launch

Install Claude Code and sign in with your Claude.ai subscription:

```bash
claude auth login
claude auth status
```

The backend checks for a logged-in, first-party Claude.ai subscription and
rejects active API-key routing. `CLAUDE_CONFIG_DIR` can select a custom
credential location; the CLI owns the
credentials and their refresh. Raw authentication metadata is not saved in run
artifacts.

From the repository root, substitute your Lean file, declaration and project:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --lean-file /path/to/Problem.lean \
  --theorem-name YourNamespace.theorem_name \
  --project-path /path/to/lean-project \
  --prover claude-code --prover-model opus \
  --refiner claude-code --refiner-model opus \
  --reasoning-effort high \
  --planner-escalation off \
  --cost-budget-usd 0
```

`--claude-code-bin /path/to/claude` selects a custom executable. Startup checks
the CLI flags, version and saved authentication without making a model request.
Use a full model identifier instead of an alias if you need a stable selection;
the final response metadata records model names reported by the CLI.

You can combine providers, for example:

```bash
--prover codex --prover-model YOUR_CODEX_MODEL \
--refiner claude-code --refiner-model opus
```

Automatic API planner escalation is disabled whenever either role uses a
subscription transport. Explicit API planner selections retain their existing
behavior. Codex and Claude Code executable choices are saved only for runs that
use those providers. Bare `--resume-from /path/to/run` inherits both choices and
rejects explicitly conflicting replacements.

This backend applies to Mini's prover and refiner roles. The natural-language
frontends' formalizer and campaign model settings remain API-backed.

## Request behavior and isolation

Each request starts a fresh, non-persistent CLI invocation with Mini's complete
serialized transcript. Mini retains checkpoint history, executes host tool
requests and checks Lean proofs. Claude returns a structured envelope containing
`content` and a `tool_calls` array. Only the final successful CLI result's
validated `structured_output` can become a prover response.

Native Claude tools are disabled except the inert `StructuredOutput` mechanism
used to serialize the envelope. Hooks, skills, plugins, browser integration and
MCP servers are disabled through safe mode and explicit CLI controls. The
adapter validates initialization, session identity, native tool names and tool
result identities. Host tools such as `check_lean` must appear inside the JSON
envelope; calling them directly as Claude-native tools is rejected.

The adapter deliberately avoids `--bare`, which disables saved subscription
OAuth. Environment credentials and provider overrides are removed. Installed
Claude Code, saved authentication and administrator-managed policy remain
trusted. These CLI settings are not an OS sandbox; rejecting an event detects a
policy violation rather than undoing an action already performed by the CLI.

## Controls and accounting

- `--reasoning-effort low|medium|high|max` maps directly to Claude Code's effort
  setting. Support depends on the selected model. Explicit reasoning-off and
  `minimal` are rejected instead of silently changing the requested policy.
  Automatic bounded-output recovery uses `low`, which the transport supports.
- Temperature and top-p are recorded as unsent. Output-token settings are
  prompt targets, not server-enforced caps.
- Claude Code caps piped input at 10 MiB. Oversized requests fail before dispatch
  instead of dropping required context. Observed CLI compaction is rejected as a
  context failure because required transcript contents can no longer be verified.
- One dispatch means one CLI invocation. Internal model turns and structured
  output retries can consume additional usage inside that invocation.
- Input counts include fresh input, cache reads and cache writes. Final CLI
  usage is counted once. If the final aggregate is missing, observed assistant
  usage is deduplicated by message ID, recorded as partial, and the response
  remains marked incomplete. Zeroed crash totals also use this fallback.
  Partial snapshots are incomplete observations, not final token totals; they
  count as one provider exposure while retaining missing-usage status.
- Usage is unpriced subscription usage. Claude Code's API-dollar estimate is
  not treated as an authoritative subscription charge. `--cost-budget-usd 0`
  is required; the account's applicable allowances and usage limits still apply.
- Request deadlines cover preflight, admission, startup and stream processing.
  Batch samples share an operation deadline. Cancellation reaps local process
  groups; terminating a local process cannot guarantee remote generation stopped.
- Proven unsent requests return their exact dispatch ticket. Missing or uncertain
  provider receipts retain conservative accounting and durable recovery behavior.

Official references: [programmatic Claude Code](https://code.claude.com/docs/en/headless),
[authentication](https://code.claude.com/docs/en/authentication),
[CLI options](https://code.claude.com/docs/en/cli-reference), and
[structured output](https://code.claude.com/docs/en/agent-sdk/structured-outputs).
