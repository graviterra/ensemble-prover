# Providers and model roles

Choose a transport for each workflow role, then select a model that transport
actually serves. Provider configuration controls generation; Ensemble Prover
retains scheduling, tool execution, Lean checks, and proof acceptance.

## Available transports

| Transport | Selection | Requirements and limits |
| --- | --- | --- |
| OpenAI API | `openai` | `OPENAI_API_KEY`; API usage and pricing when available |
| DeepSeek API | `deepseek` | `DEEPSEEK_API_KEY`; available in Mini and standalone formalization workflows |
| OpenRouter API | `openrouter` | `OPENROUTER_API_KEY` and an explicit routed model |
| Codex subscription | `codex` | Compatible installed CLI, saved ChatGPT sign-in, explicit model; [setup and limits](CODEX_SUBSCRIPTION_BACKEND.md) |
| Claude Code subscription | `claude-code` | Compatible installed CLI, saved Claude.ai sign-in, explicit model; [setup and limits](CLAUDE_CODE_SUBSCRIPTION_BACKEND.md) |
| Operator-managed inference | `local` | Registered deployment with exact model, protocol, capacity, and finite compute budget; [configuration](local-inference.md) |
| Cursor subscription | `cursor` | Recognized configuration, but generation is currently unavailable and rejected before spawning |

The CLI loads the repository's `.env`. The browser service uses its startup
environment and existing CLI sign-ins; it does not load `.env` for provider
discovery. A visible provider or valid profile does not establish successful
authentication or model compatibility.

## Roles and routing

| Workflow | Role controls | Supported routing |
| --- | --- | --- |
| Mini theorem proving and answer discovery | `--prover`, `--refiner`, their `--*-model` or `--*-deployment` settings | API, Codex, Claude Code, or local; answer discovery uses the prover |
| Mini planner escalation | `--planner-escalation`, `--planner-escalation-model`, `--planner-escalation-deployment` | API or local; defaults to `off` |
| Single-claim translation | `--formalizer`, `--formalizer-model`, `--formalizer-deployment` | API, Codex, Claude Code, or local; Mini flags follow `--` |
| Standalone campaign | `--formalizer-provider`, `--reviewer-provider`, `--prover-provider`, plus role models/deployments | API, Codex, Claude Code, or local |
| Autonomous discovery | `--provider`, `--review-provider`, `--model`, `--review-model`; local deployment flags | OpenAI, Codex, Claude Code, or local |

Cursor selections remain unavailable in all of these workflows. A CLI accepting
a provider name is not proof that its runtime transport is ready.

The Mini prover is required. The optional refiner continues the proof transcript
after stalls or rejected attempts. Ordinary recursive planning uses the prover;
planner escalation is a separate bounded response to unusable plans. Automatic
API escalation is suppressed for subscription roles. Explicitly configured API
roles still incur their normal API usage.

In discovery, the research provider/model also supplies integrated formalization,
Mini prover, and refiner work. The review provider/model supplies argument and
semantic reviewers. Review provider defaults to the research provider. A
separately launched campaign has its own role selection and budgets.

## Hosted or subscription example

For two subscription roles, replace the model placeholders with available names:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --lean-file /path/to/Target.lean --theorem-name MyNamespace.target \
  --project-path /path/to/lake-project \
  --prover codex --prover-model YOUR_CODEX_MODEL \
  --refiner claude-code --refiner-model YOUR_CLAUDE_MODEL \
  --cost-budget-usd 0
```

Subscription allowance is not priced as API dollars. Mini requires the dollar
stop disabled for subscription roles; use time, conversation, and workflow
request limits to bound work. A mixed run can still incur API charges from its
explicit API roles. A zero dollar cap does not make those calls free.

Standalone campaign roles use different flag names:

```bash
.venv/bin/python -m ensemble_prover.formalization run runs/formalization/example \
  --formalizer-provider codex --formalizer-model YOUR_CODEX_MODEL \
  --reviewer-provider claude-code --reviewer-model YOUR_CLAUDE_MODEL \
  --prover-provider codex --prover-model YOUR_CODEX_MODEL \
  --max-steps 10 --max-model-calls 30
```

Initialize the campaign first using the
[campaign walkthrough](USER_GUIDE.md#19-run-a-multi-file-formalization-campaign).
Its invocation cap is not an aggregate cap on nested Mini requests or transport
retries. Discovery provides a separate shared request authorization for its
integrated workflow.

## Reasoning and output capacity

Mini accepts a shared `--reasoning-mode` and `--reasoning-effort`, with prover and
refiner overrides. `provider-default` sends no explicit reasoning control;
it does not mean reasoning is disabled. Support for `on`, `off`, effort levels,
and temperature depends on the selected provider/model.

For maximum reasoning on the prover and refiner, add:

```bash
--reasoning-mode on --reasoning-effort max
```

Use `--prover-reasoning-effort max` or `--refiner-reasoning-effort max` to
select it for one role. In the browser launcher, choose `max` under Reasoning.
The CLI also accepts `Max` and `MAX`.

| Transport | Max request |
| --- | --- |
| Codex | `model_reasoning_effort="max"`; the legacy GPT-5 through GPT-5.5 compatibility alias remains `xhigh` |
| Claude Code | `--effort max`; availability depends on the selected model, account policy, and installed CLI |
| OpenAI API | `reasoning.effort="max"` on Responses requests; compatible Chat Completions requests use `reasoning_effort` |
| DeepSeek API | `reasoning_effort="max"` with thinking enabled |
| OpenRouter, including Anthropic models | `reasoning.effort="max"` when advertised; established DeepSeek and GPT-5.2 aliases can use advertised `xhigh` |

Max preserves the model identifier, output allowance, and run budgets. Ordinary
proof and planning requests inherit the role effort. A bounded serialization or
visibility-recovery request can use its separate lower-effort policy; the recorded
request settings distinguish it from proof search. Provider receipts show what
was sent, without guaranteeing internal compute or a model's effective effort.
Unsupported explicit controls fail instead of being dropped. OpenRouter Max
requests cannot be replaced with a lower advertised effort or generic enablement.

Max effort and Pro execution are separate selections. OpenAI documents them as
independent controls, and OpenRouter offers Pro model IDs separately. Choose an
available Pro model ID explicitly when that is the desired route; selecting Max
does not rewrite the model or add `reasoning.mode="pro"`. Mini's existing
`--reasoning-mode on|off|provider-default` controls enablement, not Pro execution.
Anthropic models are currently available through Claude Code or OpenRouter;
there is no direct Anthropic Messages API transport in Mini.

Provider references: [OpenAI reasoning](https://developers.openai.com/api/docs/guides/reasoning),
[Claude Code effort](https://code.claude.com/docs/en/model-config#effort-level),
[DeepSeek thinking](https://api-docs.deepseek.com/guides/thinking_mode/), and
[OpenRouter reasoning](https://openrouter.ai/docs/guides/best-practices/reasoning-tokens).

An output allowance limits a request, not the total run. The browser runtime
panel distinguishes configured settings, prepared requests, and completed
provider observations. Missing effective settings remain unknown. Cost output
reserves are accounting controls, not provider output-limit settings.

If a hard total output-token limit per provider invocation is required, pass
`--require-output-token-limit` to Mini. A subscription CLI that cannot enforce
that bound is rejected before generation; an internal per-request cap does not
bound the sum across its retries.

Local deployments declare reasoning, sampling, context, and output policies in
their profile. Conflicting role overrides are rejected rather than silently
reinterpreted. See [local request validation](local-inference.md#preserve-the-request-and-validate-the-response).

## Local inference and network policy

One adapter supports generic compatible chat servers, vLLM, Ollama's compatible
chat route, and llama.cpp through explicit dialects. The operator starts and
manages the server; the prover does not install weights or reserve a GPU against
unrelated processes. Shared capacity groups account for configured concurrent
requests, while a finite run allocation bounds dispatches, output requests, and
observed request time.

`--inference-policy local-only` requires all enabled inference roles to resolve
locally. It does not make the application offline. The separate
`--network-policy offline` blocks supported application-managed remote access and
downloads while permitting the bound local endpoints; it requires cached
dependencies and is not operating-system network isolation.

If an HTTP connection closes without evidence that generation stopped, capacity
can remain held as an unknown completion. Inspect and reconcile it through the
[local inference operator workflow](local-inference.md#bound-shared-compute-independently-of-api-cost).
Do not repeatedly launch replacements to work around an unresolved reservation.

## Compatibility and failures

Subscription adapters isolate CLI invocations and validate their structured
responses. Unsupported protocol events stop with an infrastructure failure.
Installing or upgrading a CLI alone does not establish adapter compatibility.
There is no automatic switch to paid API inference when a subscription fails.

Authentication, quota, malformed responses, timeouts, and protocol incompatibility
are operational failures. They do not refute the theorem. Inspect the recorded
failure kind, correct the provider setup, and use the appropriate
[resume workflow](operations.md#stop-and-resume).
