# Formalization adversarial review — 2026-09-05

Scope: the development formalization campaign and its existing Mini interfaces,
on `feature/nl-input`. No release branch, archive, or unrelated console work was
modified. This is a correctness review, not a frontier-mathematics benchmark.

## Review method

Three adversarial passes covered mathematical admission/provenance, durable
campaign state, and Mini integration. Later passes challenged earlier fixes and
their assumptions; reviewers crossed ownership boundaries. Confirmed defects
received executable failing regressions before production changes and separate
RED/GREEN checkpoints. The controller also checked CLI outcomes and ran the
combined compatibility suites.

The first pass checked admission, state transitions, and context delivery. The
second challenged those fixes across subsystem boundaries. The third reproduced
indirect-import contradictions, live-state rollback errors, and late-activated
provider failures, then independently rechecked their corrections. Successful
proof commits, prior durable proofs, unmarked Mini recovery, and genuinely queued
Lean-only verification remain positive controls.

Tests use scripted models or the real shared client with an in-process mock HTTP
transport. Mathematical witnesses use the installed Lean toolchain and isolated
temporary projects. The review does not consume paid model requests or modify
the installed Mathlib cache.

## Findings and corrections

| Boundary | Failure reproduced | Correction |
| --- | --- | --- |
| CLI | Provider/context failures returned exit status zero. | Explicit operational failures exit nonzero; ordinary budget pauses remain successful invocations. |
| Restart | A crash after freezing a reviewed statement left the old accepted review pending, repeatedly replaying proof attempts. | Freeze and pending-review removal are atomic; old matching checkpoints recover once. |
| Scheduling | An unrelated optional task's question blocked the root. | Only clarification on the root's prerequisite closure blocks completion. |
| Transport | An exhausted client retry ladder restarted as another campaign step. | Typed provider-boundary failures pause the invocation and release its lease. |
| Recursive proving | Child and grandchild provers lost the full campaign plan and cited source. | Exact canonical context propagates through recursive helpers and history clearing without repeated wrapper growth. |
| Module origin | A local module with a familiar library name inherited automatic trust. | Resolved automatic-import origins are checked; local overrides require explicitly pinned trust. |
| Target identity | A valid `_root_`-qualified theorem name failed admission/export comparisons. | Comparisons use Lean name components, preserving quoted components. |
| Compiled inputs | Rebuilding a library and restoring its source left a changed compiled artifact behind an unchanged git fingerprint. | Compiled-library build identities are included in full environment validation. |
| Module paths | A literal dot in a quoted module component selected the wrong file; invalid components could evade origin checks. | Module suffixes are appended to exact decoded paths; invalid path components fail closed. |
| Proof receipts | Initial finalization and a verified refresh in one transaction conflicted at commit. | A validated same-dossier refresh supersedes its earlier pending receipt; tampering, expiry, and unrelated participants remain guarded. |
| Live completion state | Rolling back a proof transaction cleared the dossier but left Mini reporting success from provisional session fields. | The live completion fields roll back with the proof transaction, preserving any genuinely prior completion. |
| Mini failure return | Authentication failures looked like unfinished mathematics; required-context overflow could become an indefinitely refunded scheduler wait. | Structured terminal outcomes return to the campaign, with marked campaign overflow kept terminal. Finalized proofs still take precedence over old error metadata. |
| Indirect imports | Changing a local dependency behind an unchanged git-library import allowed an old receipt to justify `False`. | Mutable compiled inputs are bound at admission and full validation; output roots are isolated, and base libraries cannot import the generated module namespace. |

The indirect-import defect was demonstrated with a real Lean contradiction in a
temporary fixture, not merely a stale metadata assertion. Its regressions check
both rejection of the old closure and rejection of a new contradictory module.
They cover project/path-package/search-path inputs, unmanaged generated-root
inputs, quoted hidden namespaces, and the reserved generated namespace itself.
Control directories are kept inside the pruned generated namespace so checking
output isolation does not enumerate accumulated lock/scratch history per module.
Rejecting an overlapping output root now happens before creating directories in
the trusted input tree.

## Verification record

The production tree was frozen at `692317c67` before the final combined runs.
The permanent regressions are `tests/test_formalization_adversarial_*.py`.

- Mini finalization/session/transaction/telemetry regression selection:
  **1,479 passed** in 61.86 seconds.
- Original NL frontend, theorem-project input, prompt support, and recursive
  helper compatibility selection: **248 passed** in 189.85 seconds.
- Independent final provenance/control-directory cross-check: **19 passed**;
  terminal and rollback cross-check: **40 passed**, plus **7** existing
  recovered/held-provider controls. No unresolved findings in reviewed scope.
- Full formalization suite: **319 passed**, no skips; combined Python line
  coverage **91.09%** (1,933 of 2,122 executable statements), exceeding the 80%
  coverage gate.
- Ruff and `git diff --check`: clean.

These selections overlap; their counts are not a combined unique-test total.
The formalization suite is partitioned into four nonoverlapping file selections,
run in separate processes, with coverage combined afterward. An equivalent
single-process command is:

```sh
./.venv/bin/pytest -q tests/test_formalization* \
  --cov=ensemble_prover.formalization --cov-fail-under=80 \
  --cov-report=term-missing
```

| Formalization selection | Passed | Seconds |
| --- | ---: | ---: |
| Universe/contract identity and guardrails | 19 | 439.06 |
| Campaign, CLI, sources, evidence, store, restart, and end-to-end export | 122 | 250.66 |
| Compiler, environment, export, and mathematical provenance | 82 | 494.02 |
| Mini integration, transport, and remaining adversarial regressions | 96 | 127.00 |

A local snapshot timing check inspected 40,602 installed compiled files and two
mutable compiled files: capture took 1.418 seconds and full validation 1.400
seconds. This single local observation is not a scale benchmark or a guarantee;
the inventory does not read all compiled payloads.

## Remaining limits

The installed toolchain and selected dependency code are trusted executable
inputs, not an OS sandbox. Build-identity inventories use file metadata and
resolved origins, not hashes of all installed compiled payloads. A same-content
rebuild can conservatively invalidate a campaign. This is not protection against
a hostile process controlling the filesystem, and weak older snapshots are not
silently upgraded.
Installed git libraries and the toolchain must remain unchanged while a campaign
is running; their full inventory checks are boundary checks, not a filesystem
lock or an atomic defense against concurrent external mutation.

The review provides no certificate that a Lean statement means the intended
natural-language mathematics, no proof that all bugs are absent, and no evidence
of million-line or FLT-level autonomous success. Those require separate semantic
evaluation and scale testing. See [the campaign guide](formalization-campaign.md)
for operation, trust boundaries, and the existing evaluation evidence.
