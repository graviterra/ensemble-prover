# Natural-language formalization campaigns

This guide covers advanced operation beyond the
[User Guide's campaign walkthrough](USER_GUIDE.md#19-run-a-multi-file-formalization-campaign).
Start there for initialization, model selection, budgets, task revision, and export.

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
rejection sends the task back for repair. Within a failed Mini attempt, cached
verified helpers may be rechecked and reused, but the campaign does not restore
the entire previous Mini search graph or its failed strategies.

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
