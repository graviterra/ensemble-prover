# Natural-language formalization campaigns

This guide covers advanced operation beyond the
[User Guide's campaign walkthrough](USER_GUIDE.md#19-run-a-multi-file-formalization-campaign).
Start there for initialization, model selection, budgets, task revision, and export.

A campaign develops definitions and supporting theorems as a dependency-ordered
project. Formalization, independent semantic review, Mini proving, and checked
module admission have distinct responsibilities. A reviewed statement or a
paused campaign is not a verified root export.

The CLI defaults to OpenAI models but accepts explicit API, Codex, Claude Code,
and local role selections. Use the [provider guide](providers.md#roles-and-routing)
for the exact role flags. Local deployments carry their finite shared compute
allocation through child proof work. Cursor generation is currently unavailable.

## Replay an exported project

Use the command in the exported bundle's `README.md`. Its form is:

```sh
cd /absolute/path/to/the/recorded/lake_project
LEAN_PATH=/absolute/path/to/my_project_export \
  lake env lean /absolute/path/to/my_project_export/Root.lean
```

Update the bundle paths if you move the export. Keep the recorded Lean,
Mathlib, and project dependencies available. Replay imports the exported
compiled modules; it does not download dependencies or rebuild every source
file. The export is not a self-contained Lake project.

`export.json` records the current root objective and the initial objective.
Check both when a task has been revised, and inspect the exported declarations
to confirm that they state the mathematics you intended.

## Run concurrent workers

Separate processes on the same machine can use the same campaign directory.
Run the usual `formalization run` command in each terminal. The shared ledger
leases ready tasks to workers; useful concurrency depends on independent tasks
being available. Each invocation has its own step and model-request limits, so
adding workers does not create a shared spending cap.

Workers renew their leases while running. Interrupt once and allow cleanup.
After a crash, wait for the lease to expire before expecting another worker
to reclaim that task. Do not manually remove leases or edit `project.sqlite3`
to force work to restart.

## Recover after proof admission fails

A completed Mini proof is saved before it is admitted as a campaign module.
Repeating `run` retries that exact saved source when the task generation,
frozen statement, and dependencies still match. It does not need to repeat
proof search merely because module admission was interrupted.

The saved proof is checked again, not trusted automatically. Repeated admission
rejection sends the task back for repair.

## Continue unfinished Mini work

Each Mini invocation writes a new generation under `proof_runs`, preserving the
previous generation's evidence. A later attempt on the same frozen statement
restores committed search state, conversation, verified helpers, provider
continuations, and consumed action budgets. Lean rechecks saved mathematical
artifacts before they become usable. Strategy review yields, cancellation, and
operational interruption retain this continuation; they do not authorize new
model work by themselves.

Continued grants use the restored state and reasoning notebook without embedding
complete prior runtime archives into each new problem description. Exact attempt
artifacts remain available through the campaign's `proof_attempt_feedback` events
and `read_event` research action, including evidence from interrupted attempts.

When proof search identifies a missing prerequisite, `expand` can add it while
preserving the parent's frozen claim. After the child is independently verified,
`retry_proof` resumes the same parent attempt and its cumulative budgets. New
modules undergo fresh Lean admission, and saved mathematical artifacts are
rechecked in the extended context. Old-context tool receipts retain their
complete candidate arguments in the reasoning notebook but cannot act as
verification authority in that context. If saved-session replay, fresh
prerequisite admission, or extended-context replay fails, the campaign returns
`continuation_error`. Subsequent
grants retry that saved proof admission before any new formalizer turn; repair
the prerequisite or checker failure to continue with the same spent budgets.

The continuation is bound to the exact frozen contract, compiled dependencies,
project inputs, and Mini options. A mismatch or unavailable checkpoint returns
`continuation_error` before Mini dispatch. Preserve the saved generation when
investigating that result. An intentionally changed contract requires a new
task or campaign; it cannot silently reset the old attempt's finite limits.
Prover and refiner model, endpoint, and transport settings are also bound. Restore
those settings to resume a campaign checkpoint; automatic provider migration is
not available through this campaign interface.

Research campaigns allocate a separate `proof_quantum_s` service interval. At
its end the formalization campaign returns `proof_quantum_exhausted`; another
authorized interval resumes the same mathematical attempt. The Python adapter
exposes this interval as `MiniProver(..., service_quantum_s=...)`. Explicit Mini
limits, including `run_wall_clock_budget_s`, remain cumulative across intervals.
Shared clients keep their existing transport and financial owner. Injecting a
second `cost_controller` or restoring an incompatible financial journal is
unsupported and fails before model work.

## Diagnose environment mismatches

Do not rebuild or replace installed base dependencies during a campaign.
Compiled-library fingerprints include filesystem build identities, so even a
same-content rebuild can invalidate the saved environment. Preserve the original
build if you need to resume; use a new campaign for an intentionally changed
environment rather than replacing recorded fingerprints.

Resolved module locations matter, not just import names. Check project search
paths and inherited `LEAN_PATH` if a local module shadows a trusted library.
Keep campaign output outside base compiled/search roots, and never import its
reserved `Formalization` module prefix from base libraries.

Use trusted local projects and dependencies. These checks assume a trusted
filesystem; generated Lean source checks are not an operating-system sandbox.
