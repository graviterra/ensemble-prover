# Local inference and Cursor availability

Local inference uses an operator-managed server through an OpenAI-compatible
chat interface. A deployment profile identifies the exact served model, its
limits, the wire protocol, and the resources shared with other requests. The
prover continues to own tool execution and Lean verification.

Use the same adapter with a generic chat server, vLLM, Ollama's compatible chat
route, or llama.cpp. Local deployment selection is available to Mini proof and
answer workflows, natural-language formalization, formalization campaigns, and
research workflows. A valid profile establishes configuration, not the quality
or compatibility of a particular model. Native tool behavior and preservation
of mathematical context still depend on the actual serving stack.

Cursor CLI is a separate subscription backend. Its current generation support
is **unavailable**: the installed CLI contract does not establish startup-hook
suppression and context preservation. Selecting Cursor fails before generation
is spawned. Installation or sign-in alone does not remove this restriction.

## Configure a deployment

Start with [the example profile](../examples/local-inference.yaml). It selects
an unauthenticated loopback endpoint and a generic, nonstreaming chat protocol.
Replace `your-served-model-id`, the context/output limits, and the template
allowance with values appropriate to your deployment. The example's numbers are
illustrative allocations, not measured capacity or recommended model settings.

The server is managed separately. The profile does not install a model, start a
server, allocate a GPU, or authorize stopping other inference processes.

The versioned YAML or JSON document has five sections:

| Section | Purpose |
| --- | --- |
| `coordinator` | Stable installation and host scope for shared capacity records. |
| `endpoints` | Connection URL, dialect, authentication reference, billing declaration, and capacity group. |
| `deployments` | Exact model identity, context/output limits, reasoning/sampling policy, and wire protocol. |
| `capacity_groups` | Simultaneous requests, queue capacity, and finite queue/request timeouts. |
| `run_budget` | Aggregate dispatch, requested-output, and observed-request-time allowances. |

Unknown fields, duplicate keys, malformed types, unsupported schema versions,
and inconsistent bindings are rejected. Model names and URL paths retain their
case. A model name resembling a hosted model does not establish that model's
context size, controls, or pricing.

Check the profile without connecting to the endpoint:

```bash
.venv/bin/python3 - <<'PY'
from ensemble_prover.local_inference.config import load_profile_path

profile = load_profile_path("examples/local-inference.yaml")
print("Valid deployment IDs:", ", ".join(profile.deployments))
PY
```

This checks configuration only. It does not verify authentication, native tools,
model availability, tokenizer accuracy, or the server's effective limits.

## Launch a proof or translation

After editing the example for your server, select deployment IDs rather than
supplying another model override:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --lean-file /path/to/Target.lean \
  --theorem-name MyNamespace.target \
  --project-path /path/to/lake-project \
  --local-inference-config examples/local-inference.yaml \
  --prover local --prover-deployment math \
  --refiner local --refiner-deployment math \
  --inference-policy local-only
```

The profile supplies the exact model, reasoning settings, output allowance,
and finite compute budget. Conflicting explicit model, reasoning, or sampling
controls are rejected. `mixed` allows intentionally selected hosted roles;
`local-only` requires every enabled inference role to resolve locally and
suppresses automatic hosted planner escalation. It does not silently choose a
hosted fallback when local inference fails.

To translate a statement without starting proof search:

```bash
.venv/bin/python -m ensemble_prover.nl_input \
  --text 'Every natural number equals itself.' \
  --project-path /path/to/lake-project \
  --output-dir /path/to/new-translation \
  --formalizer local --formalizer-deployment math_text \
  --local-inference-config examples/local-inference.yaml \
  --inference-policy local-only --formalize-only
```

Translation produces a formal statement to inspect; it does not establish a
proof. The optional `math_text` selection declares `tools: text_only`; it
shares the server and capacity group with `math`. Native-tool deployments also
support plain response phases, such as finalization and answer discovery.
Text-only deployments cannot substitute for native tool execution.
Other workflows expose their own named role/deployment flags. Use the
workflow's `--help` and select all enabled roles under `local-only`. Proof
children, answer discovery, retries, and resumed work retain their parent
allocation instead of receiving a fresh compute budget.

## Register deployments in the browser workspace

Configure the service, then select **Local** and a registered deployment in
Setup or the Launcher:

```bash
export ENSEMBLE_LOCAL_INFERENCE_CONFIG=/path/to/local-inference.yaml
.venv/bin/python -m interface.service --control
```

The service loads the operator profile at startup and freezes its configuration
for launches. Restart the service to adopt changes to the source profile. The
browser receives deployment IDs, declared models and limits; it does not accept
endpoint URLs, configuration paths, or credentials. Defaults and drafts retain
the selected deployment. English input has a separate formalizer selection.

Catalog discovery does not contact an inference endpoint. **Declared, not
probed** means exactly that; a visible deployment is not a successful connection
or tool-compatibility check. The live run view shows per-role queue, generation,
and uncertain-completion observations separately from mathematical progress.
Cursor remains unavailable in both the UI and launch API until its generation
contract can be qualified.

## One adapter, explicit dialects

The chat protocol supports four selectable dialect contracts. They describe
which declared wire fields may be sent; they do not certify every model or
server version bearing the name.

| `dialect` | Explicit reasoning request fields allowed by the contract |
| --- | --- |
| `generic` | `reasoning_effort` |
| `vllm` | `reasoning_effort`, `chat_template_kwargs.enable_thinking` |
| `ollama` | `reasoning_effort` on the OpenAI-compatible chat route |
| `llamacpp` | `reasoning_effort`, `chat_template_kwargs.enable_thinking`, `reasoning_format` |

The Ollama dialect does not translate controls into a native `/api/chat`
`think` field. Reasoning field values must be declared for the actual model;
the adapter does not infer them from a model name or silently discard a
requested control.

`reasoning.mode: provider-default` sends no explicit reasoning control.
Explicit `on` or `off` requires a corresponding mapping under
`protocol.reasoning_controls`. A requested effort also needs a mapping under
`protocol.reasoning_efforts`. Conflicting mappings fail configuration validation.
For a deployment that actually supports the declared values, a generic mapping
could be:

```yaml
reasoning:
  mode: on
  effort: high
  output_limit_includes_reasoning: unknown
protocol:
  schema: 1
  reasoning_controls:
    on: {reasoning_effort: high}
    off: {reasoning_effort: none}
  reasoning_efforts:
    high: {reasoning_effort: high}
```

This is an illustrative replacement fragment, not a statement that `high` and
`none` work on your server. Other protocol fields retain their defaults when
omitted. Sampling is declared independently for `temperature` and `top_p`:
`unrestricted`, `forbidden`, or `fixed` with an explicit `value`.

Automatic Mini phase temperatures, including custom programmatic phase
strategies, follow the deployment's fixed or forbidden policy. Telemetry retains
both the strategy's requested value and the effective deployment value. Explicit
CLI sampling conflicts are rejected during admission; direct client overrides
remain strict. An unrestricted deployment allows phase temperatures normally.

## Preserve the request and validate the response

Native tool calls use the selected model's chat interface. Tool names and JSON
arguments must validate as a complete batch before any tool executes. Text
that merely resembles a tool call is not native tool authority. Lean remains
the authority for proof acceptance.

The protocol policy includes:

- Exact response `model_aliases`, empty by default. An arbitrary response model
  is not treated as an alias.
- `argument_encoding: json_string` by default, or explicitly declared `object`.
- Declared `history_replay_fields` and `require_history_replay` for supported
  reasoning-continuation fields. Replay support varies by dialect.
- `template_overhead_tokens` and bounds for response bytes, stream events,
  argument bytes/depth, and tool-call count.
- Optional streaming with explicit `require_done` and `usage_request` policy.
  `include_usage` applies only when streaming is enabled. Partial stream data
  does not authorize tool execution.

Configured context and template allowances are operator declarations. Estimated
prompt counts are not an exact tokenizer guarantee. Required mathematical
context must not be discarded to make a request fit. A server silently
truncating that context is incompatible with the requested workflow.

## Check a deployment explicitly

The operator CLI separates passive inspection from a bounded live check:

```bash
.venv/bin/python -m ensemble_prover.local_inference.readiness_cli show \
  --snapshot /path/to/run/local_inference/private_snapshot.json

.venv/bin/python -m ensemble_prover.local_inference.readiness_cli probe --help
```

`show` reads the saved selection without contacting its server. Add
`--receipt /path/to/receipt.json` to display a previously saved conformance
receipt. Its deployment identity and expiry must still match.

`probe` requires explicit finite output, dispatch, and wall-time allowances and
a fresh setup-budget identity. It sends two exchanges: a native tool request,
then a synthetic tool result and final-response request. No mathematical tool
is executed. For example, using the coordinator directory recorded in the
run's private `local_inference/run_binding.json`:

```bash
local_probe_id=$(.venv/bin/python -c 'import secrets; print(secrets.token_hex(16))')
local_probe_now=$(date +%s)
.venv/bin/python -m ensemble_prover.local_inference.readiness_cli probe \
  --snapshot /path/to/run/local_inference/private_snapshot.json --role prover \
  --coordinator-root /path/to/operator/coordinator \
  --budget-root "/path/to/operator/probes/$local_probe_id" \
  --budget-id "$local_probe_id" \
  --max-output-tokens 256 --max-dispatches 2 \
  --max-requested-output-tokens 512 \
  --max-observed-request-wall-s 120 --request-timeout-s 60 \
  --now "$local_probe_now" --expires-at "$((local_probe_now + 3600))" \
  > /path/to/receipt.json
```

A `bounded_pass` records that exchange only. It does not certify mathematical
ability, the full context window, reasoning-control enforcement, output-limit
enforcement, or future availability. Expired or mismatched evidence does not
become current readiness. A probe spends its own finite setup allocation and
shares capacity with other requests using that coordinator.

## Authentication and evidence

For an endpoint requiring authentication, replace `auth: {kind: none}` with an
explicit environment-variable reference:

```yaml
auth:
  kind: env
  name: LOCAL_LLM_API_KEY
```

Set that variable in the process environment through your normal secret
management. Do not put its value in YAML, command arguments, or a model name.
Cloud-provider credential references are rejected; an unrelated cloud API key
is not reused implicitly for local inference.

Identity fields such as `revision`, `server_build`, `tokenizer_id`,
`template_id`, `parser_id`, and `quantization` are optional. Omitted identities
remain unknown. Supplying a value records configured evidence, not a discovered
or independently checked fact.

Profile, deployment, and capacity identities serve different purposes. Private
worker snapshots retain the connection configuration and credential reference;
public manifests omit URLs and credential-reference names. Changing a protocol
or serving identity changes the deployment fingerprint. Resume/reconfiguration
must retain the allocation already consumed rather than start a fresh budget.

## Bound shared compute independently of API cost

`billing.kind: owned_compute` declares zero marginal API dollars. It does not
claim zero electricity, hardware, hosting, or opportunity cost. `metered`
billing instead names a tariff and version; a tariff reference alone does not
establish a verified dollar price.

The local allocation tracks three separate quantities:

- **Dispatches:** each concrete admitted model request consumes a unit.
- **Requested output tokens:** the admitted output allowance is charged, not
  only the tokens eventually reported by the server.
- **Observed request wall time:** time accumulated across requests, including
  concurrent requests. This differs from total elapsed run time and GPU time.

The allocation ledger reserves finite wall-time grants before dispatch and
conserves them across parent/child users of that ledger. Resume does not refill
it. A completed request can release unused wall-time reservation; a dispatched
request does not refund its dispatch or requested-output envelope. Missing
usage stays unknown.

Capacity groups separately bound simultaneous admitted requests to shared
resources. Multiple model aliases on the same GPU should share the same
operator-owned group and coordinator. These are host-local controls; they do
not coordinate arbitrary clients or machines outside that scope.

Closing an HTTP connection does not prove remote generation stopped. Unknown
completion retains its capacity reservation. Use the operator CLI's `inspect`
command to examine the recorded group and budget, then `reconcile` for a
specific unresolved dispatch. `retain_unknown` leaves capacity held;
`completion_evidence_lost` explicitly releases it with uncertainty recorded,
without refunding consumed allocation or asserting successful completion.
`settle-wall` applies only to a response whose completion is already recorded
and requires a wall-time receipt. Each command has `--help` for its required
identity and ledger arguments. The prover does not stop an externally managed
inference server to release a slot.

## Local inference is not an offline guarantee

`execution: operator_asserted_local` records where the operator says inference
runs. A local URL might still proxy another service. The `local-only` inference
policy rejects selected deployments declared as hosted upstream; it is not an
operating-system network sandbox or proof of an air-gapped setup.

Offline operation also depends on every enabled workflow, retrieval assets,
Lean dependencies, and any external tools. Keep inference locality separate
from those network requirements. Likewise, an HTTP request limit does not
reserve GPU memory against embedding or reranking models loaded elsewhere.

For application-managed offline operation, add `--network-policy offline` to
a supported CLI launch together with `--inference-policy local-only`. The
command requires cached Lean/toolchain assets and preserves the policy across
owned child workflows and resume. It blocks remote literature access, live
pricing-catalog fetches, embedding/reranker downloads, and dependency downloads
through owned Lean launches, while allowing the explicitly bound local
inference endpoints. The default network policy does not impose those blocks.

This is narrower than operating-system network isolation. Arbitrary project
code and subprocesses outside the controlled boundaries remain outside the
policy. Cached dependencies and retrieval models are still necessary. Never
interpret a local URL or an application policy as proof that an external server
has no upstream access.

Cursor is hosted subscription inference and cannot satisfy `local-only`. Its
configuration requires an exact model name; `auto` and an unspecified CLI
default are not accepted. Generation currently fails closed before spawning
`agent`, including when a different role could otherwise start work first.
