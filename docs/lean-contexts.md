# Lean verification and closure scheduling

Every complete proof check audits all declarations introduced by its helper
context and candidate, including unused declarations and generated auxiliaries.
The audit traverses shared kernel dependencies once and reports their axiom union.
The target's exact axioms are computed separately. `LeanResult.axiom_audit`
contains target provenance and any explicitly requested helper provenance;
`audited_declarations` contains the complete inventory, and `context_axioms`
contains its combined dependencies. Request helper provenance with
`LeanRunner.check(..., axiom_provenance_names=[...])` when needed.

The versioned audit binds the original target, ordered sources, environment,
request, and verification policy. Missing or inconsistent reports fail closed.
Source admission, target equivalence, answer visibility, and final export checks
continue to apply independently.

## Retaining Lean contexts

`--lean-warm-contexts` enables bounded persistent Lean documents for tactic
search with durable candidate continuations. It is disabled by default. A stable
prefix contains the trusted checker and ordered helper context; each candidate
replaces the previous candidate's suffix. Source admission uses a separate
document. Appending helpers retains the unchanged command prefix. Replacing or
reordering helpers rebuilds the affected suffix; target, environment, or policy
changes select a separate context. Slot reuse never substitutes for the complete
ordered-source binding in each audit. Completion requires the current document
version, completed Lean work, and the bound audit report.

Every successful warm candidate receives an independent fresh reference check.
Completed-success caches cannot satisfy this confirmation. If the confirmation
runs out of time, the tactic cursor retains that candidate. A resumed cursor
requests fresh reference verification directly, including after a worker restart.
`LeanRunner.check(..., force_reference=True)` explicitly selects this path.
Direct API callers can opt in with `allow_pending_reference_confirmation=True`
when they retain and resume pending candidates. Other authoritative callers use
reference execution with ordinary exact-result caching, so an unfinished warm
confirmation cannot discard their proof. Aggregate auditing applies to all paths.

`--lean-context-workers` controls the worker count, from 1 to 32; its default is
one. YAML `lean` configuration also supports:

| Setting | Default | Behavior |
| --- | ---: | --- |
| `persistent_context_slots` | 4 | Retained documents per worker |
| `persistent_context_max_rss_mb` | 16384 | Recycle a worker when its measured process-tree RSS exceeds this bound |
| `persistent_max_message_bytes` | 16777216 | Maximum host protocol frame |
| `persistent_lsp_max_message_bytes` | 33554432 | Maximum Lean protocol message |
| `persistent_transport_failure_threshold` | 2 | Repeated transport failures before temporarily bypassing persistence |
| `persistent_transport_circuit_cooldown_s` | 60 | Time before retrying a failed persistent capability |

RSS includes shared mapped pages in each process. Mathlib contexts can therefore
reach the configured RSS bound before their exclusive resident memory reaches it.
Worker count multiplies the potential memory allowance. Timeouts, cancellation,
worker recycling, and environment changes discard live context handles. A failed
transport gets one reference fallback within the original deadline; large or
truncated authority messages are rejected rather than treated as success.
Backend dispatch rechecks the runner's lifecycle after resource waits. If a warm
proof is ready when its runner is retired, its pending reference confirmation
remains available for a later check.

The programmatic `prove_theorem_project` API accepts `lean_warm_contexts`,
`lean_context_workers`, `closure_service_slice_s`, and `research_reserved_turns`
when it constructs a runner. When injecting a runner, configure its `LeanConfig`.

## Scheduling complete work

Each executed action slice records elapsed service even when its portfolio is
unfinished. Completed mathematical attempts are counted separately from service
receipts. Parent-inclusive time governs scheduling and admission; exclusive wall
service subtracts the union of nested child intervals. Background research worker
time has a separate scope because it can overlap proof work. Checkpoint recovery
preserves physical costs while rejecting stale mathematical mutations.

Diagnostic scheduler traces retain cumulative resource metrics and bounded local
history cursors. These cursors support live recovery and read-only selection
replay. Portable restart checkpoints retain the complete execution receipts and
their deduplication identities.

`--closure-service-slice-s` defaults to 30 seconds. It is a soft scheduling slice:
an admitted check keeps its full timeout, then yields before starting another
candidate. Set it to zero to disable this interleaving limit. Saved finite
portfolios and learned timeout allowances survive append-only helper growth.
Each remaining candidate is checked in the current ordered context. Helper
replacement, reordering, target changes, and environment changes invalidate the
affected generation. New generations admit fresh opportunities and a bounded
refresh of previously served candidates. Deferred candidates retain their exact
proof text and service order. Helper growth and funded provider dispatches grant
further exploration; closure dispatches alone cannot renew that allocation.
Resource-inconclusive checks remain eligible for a larger allowance. Renewed
checks receive that larger opportunity within the existing deadline; insufficient
remaining time preserves the candidate and its suffix. Already checked proofs
retain their finalization priority.

`--research-reserved-turns` defaults to zero. A positive value reserves research
capacity from existing eligible role allocations, while retaining capacity for
subsequent proof work. It adds no model calls to the configured allowance.
Unused reservations are released, and checkpoint replay cannot renew spent
capacity. When authoring capacity is exhausted, `draining_checked_work` identifies
the remaining deterministic work. A final finite drain admits deferred candidates
under the existing time allowance, preserving opportunities from implicit
instances and simplification rules in the final helper context.
All phases of that final drain share one elapsed deadline. Advancing between
active targets, lifted proofs, and root candidates does not renew the allowance
or discard retained work.

Timing records distinguish source admission, proof and audit, total check time,
and backend queue/startup/service spans. Settled background restart time and
active restart counts are reported separately because backend maintenance can
overlap action work. Pool acquisition and disposal also retain elapsed totals
and pending-work metrics, including cleanup after a cancelled cold start. These
metrics follow the runner across generation replacement and remain separate
from additive action charges. Per-check stages may contain nested spans; they
should not be added to exclusive action service. Faster verification
does not by itself establish a higher solve rate. Warm contexts and research
reservation remain explicit options for evaluating a workload's memory,
latency, and search tradeoffs.
