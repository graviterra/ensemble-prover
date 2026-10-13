# Retrieval, theory, and mathematical memory

Reusable mathematics needs more than similar wording. A candidate lemma must
have suitable assumptions, fit the active obligation, and be valid in the
current Lean environment. Ensemble Prover separates finding candidates,
checking applications, retaining verified source, and learning from experience.

## Four different kinds of reuse

| Facility | Stores or searches | Default | What a hit means |
| --- | --- | --- | --- |
| Mathematical retrieval | Mathlib and configured project declarations; lexical, structural, type-directed, and optional learned signals | Enabled | A potentially relevant declaration, not a successful application |
| Verified-helper cache | Saved same-problem helper source | Enabled | A candidate helper that must pass current Lean rechecking before admission |
| Mini theory | Content-addressed, independently checked reusable bundles | `build` | A compatible checked bundle, subject to current import and environment policy |
| Mathematical memory | Applicability profiles, application observations, use, obstructions, proposals, and notes | `off` | Eligible evidence to guide work; never a replacement for proof checking |

Retrieval and Mini theory remain useful with mathematical memory off. Memory
does not automatically make every historical proof transferable to another
problem.

## Finding and applying declarations

The model can search mathematical libraries, inspect declaration types, try a
retrieved declaration against the active goal, test scratch Lean code, and
evaluate bounded examples. Repair-time retrieval can use concrete Lean errors.
An application probe reports what it established and which obligations remain.
Residual goal text alone is advisory; checked continuations and ordinary proof
acceptance retain their separate roles.

The minimal installation supports core lexical and structural retrieval.
Learned embedding/reranking dependencies are optional. Missing optional engines
or an empty query result do not establish that no useful theorem exists.

Control the search pool with `--mini-retrieval-project-root`,
`--mini-retrieval-cache-root`, and the `--mini-retrieval-*` options. Eager
`--premise-retrieval` and the separate `--proof-state-retrieval` scheduler action
are opt-in. See the [retrieval reference](USER_GUIDE.md#9-retrieval-tools-and-caches).

## Mini theory and helper promotion

Mini theory uses `~/.cache/mini_prover/theory` unless
`--mini-theory-root` selects another store.

| Mode | Behavior |
| --- | --- |
| `off` | Disable Mini theory |
| `read` | Load compatible verified bundles without constructing missing theory |
| `build` | Permit bounded construction and independent checking of needed theory |

Use `--mini-theory-domain` to select a mathematical domain and repeat
`--mini-theory-bundle` for exact bundles. Separately enable
`--mini-theory-promote-verified-helpers` to stage eligible generic helpers from
proof work for independent publication checks.

Promotion captures the helper's context and dependencies. A theorem that depends
on a problem-specific or hidden benchmark constant cannot become generic merely
because its name looks reusable. Complete declaration names, local notation,
attributes, and instances matter to the reconstructed source. Publication
requires policy checks and fresh Lean verification.

Historical context that cannot be safely recaptured stays deferred. The
`promotion_context_recapture_required` diagnostic calls for restaging from the
original session context, not editing the receipt or declaring the old helper
portable. See [promotion recovery](USER_GUIDE.md#persistent-mini-theory).

## Memory modes

| `--mathematical-memory` | Added behavior |
| --- | --- |
| `off` | No mathematical-memory catalog activity |
| `observe` | Record existing operations and outcomes without starting extra application work |
| `assist` | Allocate bounded candidate retrieval and Lean application probes |
| `develop` | Also permit allocated generalization work with independent verification |

Start by observing or assisting one attempt:

```bash
.venv/bin/python -m ensemble_prover.mini_prover \
  --lean-file /path/to/Target.lean --theorem-name MyNamespace.target \
  --project-path /path/to/lake-project --prover openai \
  --mathematical-memory assist --mathematical-memory-seconds 90
```

The total memory action allowance defaults to 90 seconds and is shared by the
attempt and its samples. It operates within the governing run limits.
Development additionally requires Mini theory build permission and a positive
research allocation contained within that total:

```text
--mathematical-memory develop --mini-theory-mode build
--mathematical-memory-seconds 90 --mathematical-memory-research-seconds 30
```

These are flags to add to the complete launch command. They authorize bounded
work; they do not guarantee that a useful generalization will be found.

The default catalog is
`~/.local/share/ensemble-prover/mathematical-memory`. Change it with
`--mathematical-memory-root`. Campaign and family identifiers can organize scope
and eligibility; sharing an identifier does not grant proof or disclosure
authority.

## Applicability, use, and failure

Memory retains a lemma's statement, context, applicability conditions, and
observations about actual applications. Candidate ranking can use the obligation
and prior outcomes, but a promising score cannot discharge missing assumptions.

Keep these outcomes separate:

- A declaration was retrieved: it may fit the goal.
- An application elaborated: inspect remaining goals and acceptance status.
- A checked consumer used the helper: Lean observed it in the accepted proof.
- A tactic or application failed: this recipe failed under its recorded context
  and resources; the theorem may still be useful.
- A claim was refuted: this requires separately admitted evidence proving its
  negation, with the exact scope and assumptions.

Use observations distinguish root consumers from intermediate helpers. They
measure consumption, not necessity. The absence of an observation is not evidence
of uselessness. Notes and failed routes can guide a future investigation without
being promoted to mathematical truth.

Generalization likewise has two obligations: the proposed broader theorem must
independently check, and any claimed specialization link must check separately.
Several successful examples, a model review, or frequent use cannot publish a
general theorem.

## Admitting imported source

For registered Mathlib and project sources, memory can establish a live source
receipt by compiling the exact source in an isolated output directory under its
original module name. It compares the resulting kernel declarations, including
their types and bodies, with the installed module. A source file containing a
matching declaration name or printed type is insufficient.

The receipt binds the source, compiled artifact parts, current context, imported
dependency closure, and Lean module resolution. A changed artifact or a newly
shadowed dependency invalidates reuse. Receipt consumption rechecks dependency
bytes as well as file identities and resolved locations; writes through an
already writable memory mapping need not change file timestamps. Large import
closures therefore consume additional checking time within the existing allowance.
Profiling and application still require a current receipt, and the final proof
still passes the ordinary Lean acceptance path.

Source compilation, goal capture, and application use the existing memory
allocation. A candidate-specific admission failure allows other candidates to be
considered. Checker outages retain retryable work; an unaffordable retry does not
block independent requests that fit the remaining allocation. Stale requests are
settled before further checking or model dispatch.

A source file missing before its first admission, exceeding the source byte limit,
or containing invalid UTF-8 rejects that candidate alone.
Previously bound source or artifact storage becoming unavailable defers acceptance.
Catalog deadlines and database availability failures also defer source admission.
An affected root proof remains an inert candidate in the session and reasoning
notebook. Recovery uses the existing memory allowance for current source admission
and a fresh Lean check, including after checkpoint restoration. Checked helper and
theory source descriptions survive ordinary checkpoints as inputs for current
admission, even when no root proof was pending. A resumed memory pass funds this
readmission before retrieving more candidates. Current live bindings remain usable
after a checkpoint; rejected inventories do not repeatedly consume recovery work.
If an originally denied source becomes eligible again, its existing recovery
allocation can resume. A fresh exact proof-use observation can still establish
that an unrelated retained helper is unused by the root proof.
Helper recovery preserves the original declaration order, and an interrupted
recovery retains completed admissions within the live process. Removed helpers
without remaining source obligations are not reintroduced. Stored certificates
never authorize this retry. A changed source policy rejects acceptance, and a
matching previously completed root loses its current solved status until the
ordinary acceptance checks succeed again.

Source rejection parks the retained proof text until its context or source
eligibility changes. Replacing or removing a helper keeps that text available
for a fresh check against the current helper context. Malformed recovery rows
are isolated as inert diagnostics while valid source descriptions remain
available for admission. None of these recovery records replaces a Lean check.
A completed failed check pauses that proof in its checked context; checker
timeouts remain retryable, and a changed checker environment permits a new check.

These checks use the configured Lean project and installed toolchain. Configured
Lean source retains the runner's existing execution permissions; isolated output
paths do not sandbox metaprogram IO. Live receipts belong to the current process
and source context, and do not establish portable cross-problem authority.

## Cross-problem limits

Portable memory requires current authority for its full source ancestry,
permissions, revocations, and reconciliation state, in addition to artifact
integrity. The standard CLI does **not** install a trusted live source-authority
adapter. Its learned application history therefore does not automatically
transfer across problems or process restarts. Eligible session-local observations
remain useful; existing Mini theory and verified-helper retrieval are separate.

Applications with a trusted registry can provide an adapter; the
[interface integration example](../interface/README.md#starting-and-reading-attempts)
documents that boundary. A callback that simply returns true is not a valid
implementation of current authority.

Restoring a catalog does not restore live permission or mathematical authority.
Restored history stays unavailable for reuse until the relevant eligibility and
invalidation state is reconciled. Benchmark answer restrictions and source
visibility remain in force in every mode.

## Browser controls and maintenance

The **Mathematical memory** panel separates candidates, application observations,
unresolved conditions, generalization proposals, and notes. Owned runs with
control enabled accept durable pin, note, retry, and generalization requests.
Request completion is operational status, not a proof badge. Retries refer to an
existing recorded application and use remaining allocation.

The service's `--memory-root` selects its trusted catalog; owned launches inherit
that root. Evidence copied for inspection is still checked against current
source eligibility. Pausing ordinary observation updates does not freeze
permission checks.

Inspect or back up a catalog without running a prover:

```bash
.venv/bin/python -m ensemble_prover.mathematical_memory \
  --root /path/to/memory inspect

.venv/bin/python -m ensemble_prover.mathematical_memory \
  --root /path/to/memory backup /path/to/new-backup
```

The maintenance CLI also exposes `restore`, `rebuild`, and bounded outbox
`drain`; consult their help before changing stored state. Backups contain
mathematical source and evidence. Keep them within the same intended privacy
scope as the original catalog, and use separate stores for unrelated private
projects or experiments.
