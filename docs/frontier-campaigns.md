# Sustained mathematical investigations

Long investigations need to preserve unfinished mathematics through changes of
approach, formalization failures, interrupted service, and model replacement.
The proof dossier, research ledger, and durable Mini attempt have distinct roles:
the dossier records checked declarations and open proof obligations; the research
ledger records investigations and their evidence; the Mini attempt owns execution
state and cumulative resource use.

## Work whose usefulness is uncertain

With adaptive research enabled, an independently reviewed inconclusive report can
continue under the existing campaign authorization. Missing progress metadata
leaves its value unknown. This continuation does not claim mathematical progress
or add resources: deadlines, spending limits, retry limits, fairness, and scoped
holds still apply. A report can authorize its successor once; replaying the report
does not create another allocation.

Treat these questions separately:

| Question | Evidence and effect |
|---|---|
| Is the statement proved? | Checked source and its exact assumptions determine proof authority. |
| Does it advance this conjecture? | A checked dependency or reviewed argument explains the connection; an unknown connection remains unknown. |
| May investigation continue? | Campaign authorization and remaining resources govern further work. |
| Did execution fail? | Provider and checker failures describe service conditions, without refuting the mathematics. |

A checked implication remains available through ordinary helper lookup even while
its premise is unresolved. Using it still requires discharging that premise.
The number of available lemmas does not establish that the original conjecture
has been proved.

## Keeping arguments through formalization

Before proof histories are compacted or retired, the reasoning notebook retains
visible arguments, local assumptions, tool requests, and diagnostics in their
original order. Models can retrieve this inert history with
`read_reasoning_notebook`, using its query and pagination fields. A page's
`snapshot_id` keeps later pages attached to the same saved prefix while new work
is appended.

Readable reasoning text and reasoning summaries are retained alongside visible
answers. Switching between proving and refinement on the same target preserves
unfinished paid tool calls, so a local checker retry can continue without a new
model request.

Notebook entries carry no proof authority. An identifier error or failed tactic
records a formalization problem; it does not establish that the accompanying
mathematical idea is false. The notebook survives ordinary checkpoint restoration
and explicit provider migration. Opaque provider continuation data is not a
portable mathematical record.

## Requesting a local lemma

A native investigator can request a small, explicit Lean proposition before it
has a complete proof plan for the root conjecture:

```json
{
  "action": "request_local_proof",
  "lean_statement": "∀ n : Nat, n + 0 = n",
  "contract": {
    "statement": "Adding zero preserves a natural number",
    "domain": "Nat",
    "hypotheses": [],
    "quantifiers": ["for every natural number n"]
  },
  "proof_plan": "Use the defining equation for addition. The later application is still being investigated."
}
```

Include every variable and assumption in the Lean proposition. The informal
contract records intended meaning; checking the Lean proposition does not itself
certify that interpretation.

The request retains its originating job, claim revision, approach, and exact
formal context. The existing proof scheduler handles it within its current
allocations. Revised hints for the same task preserve prior attempts and reach
the proof scheduler as candidate guidance. An already
delivered attempt result remains available while the investigator supplies a new
hint; repeating the request does not wait for a duplicate result. Checked
results and inconclusive feedback return to the originating investigation through
the research ledger, including after restart. The result certifies only the local
Lean statement and leaves root completion to the ordinary verifier.

This action is available to native investigator jobs with a host-recorded formal
context. A task waits if that context is unavailable. It does not automatically
translate the request into another context or start a separate proof budget.
An environment change preserves the original task and its attempts. Previously
delivered proofs become explicit prior-context history until the original
context returns and their checked sources can be validated again. A damaged
task record is fenced independently, allowing other tasks to continue. Its
investigator receives an operational failure result and can revise the request
or continue other research; that result does not refute the local statement.

After a verifier retry defers, the proof scheduler allows competing search work
to run and then returns to the waiting verification. This service order survives
restart, retains periodic exploration, and uses the existing action budgets.

## Changing models during an investigation

Native investigation and review can use independently selected clients through
`--research-provider`, `--research-model`, `--research-review-provider`, and
`--research-review-model`. They share the run's authorized resources and inference
policy. Separate role configuration enables independent criticism; disagreement
still needs to be resolved through mathematical work and evidence.

An explicit `--resume-migrate-providers` handoff can change the selected provider
or model while continuing the same durable Mini attempt. It retains checked
mathematics, pending local tool ownership, and cumulative accounting, and retires
old provider-specific continuation envelopes. See the
[resume instructions](USER_GUIDE.md#13-replay-and-interruption-behavior) for the command
and compatibility requirements.

## Mathematical and physical claims

For a physics conjecture, record the adopted mathematical model, assumptions,
domain, and intended interpretation in its contract. Numerical experiments and
research reports can motivate a construction or reveal an obstruction. Their
results remain evidence for investigation until the required exact statement is
checked. A proof of a formalized model is distinct from establishing that the
model describes a physical system.

Use difficult known problems and research-shaped tasks to evaluate idea
retention, continuation across interruptions, useful partial results, and checked
completion under comparable resources. A benchmark that supplies the mathematics
measures infrastructure. It does not measure a model's
ability to discover the proofs of frontier conjectures.
