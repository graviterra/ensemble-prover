# Natural-language formalization campaigns

This experimental module turns UTF-8 mathematical documents into a resumable,
multi-file Lean development. It can construct definitions and supporting
theorems before the final statement is expressible. It is separate from the
single-theorem `ensemble_prover.nl_input` frontend. Both are included in release
1.07; older Mini-only releases do not include them. For a copy-and-run walkthrough, see the
[User Guide](USER_GUIDE.md#19-run-a-multi-file-formalization-campaign).

The interface is small; project size is not limited to one prompt, one proof
graph, or one Lean file. This is infrastructure for long mathematical projects,
not a demonstrated ability to autonomously formalize Fermat's Last Theorem.

## Start and resume

Run from the repository root containing `.venv/` and `ensemble_prover/`, not
from inside the Python package. Replace `lean_project` below with your existing,
built Lake project with Lean and Mathlib installed; no project is bundled.
The existing
repository `.env` credential loading applies. By default formalization and
independent semantic review use OpenAI API model `gpt-5.6-terra`; Mini proof
search uses `gpt-5.6-luna`. Set `--formalizer-model`, `--reviewer-model`, and
`--prover-model` on `run` to use other OpenAI API model names.

```sh
.venv/bin/python -m ensemble_prover.formalization init \
  --project-path lean_project \
  --source examples/formalization/finite_differences.md \
  --goal 'Formalize and prove the complete theorem in the supplied document.' \
  --output runs/formalization/my_project

.venv/bin/python -m ensemble_prover.formalization run runs/formalization/my_project \
  --max-steps 100 --max-model-calls 300

.venv/bin/python -m ensemble_prover.formalization status runs/formalization/my_project
.venv/bin/python -m ensemble_prover.formalization task runs/formalization/my_project root
```

Repeat `run` to resume. Completed project components are reused, not reproved.
`--source` accepts local UTF-8 text files and can be repeated for natural-language
problem statements, conjectures, notes, Markdown, papers already converted to
text, or LaTeX source. LaTeX is supplied as text, not processed by a TeX parser.
Original contents and line endings are preserved. PDF/image/OCR extraction,
URL downloading, and external literature acquisition are not implemented here.
Use repeated `--import Module.Name` at initialization for trusted project modules.

Each `run` defaults to at most 100 controller steps and 300 formalizer/reviewer
requests. `--max-steps` and `--max-model-calls` change those per-invocation budgets.
The latter does **not** bound nested Mini proof-search calls, which have their own
turn limits, or count individual transport retries. Neither option is a monetary
spending cap. These are explicit execution quanta, not mathematical-text limits.
`--model-timeout-s`, `--lean-timeout-s`, and `--lease-s` control operation
deadlines and worker leases. Interrupted workers release their leases; crashed
workers' leases expire. Separate processes can work on the same project ledger.

The shared transport's model-capability output envelope is preserved; no smaller
campaign-specific output limit is imposed. Provider-truncated responses are
recorded but never admitted. A required context that cannot fit must be
decomposed or explicitly retrieved differently, not silently shortened.
Provider failures and required-context overflow pause the campaign and make
the CLI exit nonzero; ordinary exhausted step/model budgets remain resumable
pauses with exit status zero. Provider failures are not evidence that a theorem
is unprovable and must not start another proof attempt in the same invocation.

## Clarifications and changes

`needs_clarification` means essential mathematical information is missing.
Inspect the relevant failed task and its recorded question. An explicit revision
supplies corrected instructions and invalidates that task's dependent results:

```sh
.venv/bin/python -m ensemble_prover.formalization revise runs/formalization/my_project root \
  --description 'Complete, corrected mathematical objective and assumptions.'
```

Do not edit the ledger or admitted modules to change a theorem. A changed Lean
environment causes an explicit error; do not overwrite its recorded fingerprint
to make old results appear valid. Start a new campaign against the new environment.
This also applies to older snapshots that lack the current provenance records:
they are rejected rather than silently upgraded to trust today's environment.

## What is checked

- Source documents are immutable, indexed, and cited by exact character ranges.
  Search pages never replace the original text. Task descriptions, proposed
  statements, proof plans, and model responses remain complete in the dossier.
- Independent model review checks the translation against the task and sources.
  It can retrieve dependency declarations and original evidence itself. Its
  judgment is **not a certificate of natural-language equivalence**.
- A reviewed proposition is compiled into an immutable Prop-valued definition.
  This binds its elaborated meaning, including chosen typeclass instances. It
  does not assume or prove the proposition. Later imports cannot reinterpret it.
- Mini receives the full accepted proof plan, original cited text, and that
  frozen target. Only Mini's finalized proof with its verified helper closure is
  submitted for independent module compilation and exact-target checking.
  Recursive helper provers inherit the same complete campaign context, even
  after conversation history is cleared. Required text is not summarized or
  trimmed to make a smaller model's request fit.
- Exact-target checking supports universe-polymorphic statements. Expected
  universe parameters stay fixed while a sufficiently general proof may
  specialize its own parameters; monomorphic or collapsed-universe substitutes
  for a more general statement are rejected. Lean's kernel checks the resulting
  proof against the promised type.
- A component is admitted only after Lean checking, allowed-axiom auditing,
  environment checks, and durable artifact publication. Unproved helper tasks
  are never made available as axioms. Final status validates the entire reachable
  compiled-module closure, not merely the root file.

The trusted Lean toolchain, Mathlib, and explicitly selected project dependencies
remain part of the trust boundary. Generated-source checks are not an operating
system sandbox. Do not treat arbitrary untrusted Lean projects as harmless data.

Environment provenance binds resolved module origins as well as configuration
and source state. A familiar module name alone does not make a local shadow a
trusted library. Installed compiled-library inventories use per-file filesystem
build identities, not hashes of every compiled payload; a same-content rebuild
can therefore conservatively invalidate a snapshot. This assumes a trusted
local filesystem and does not defend against a hostile process controlling it.
Mutable project, path-package, and inherited `LEAN_PATH` compiled inputs are
checked at admission. Installed git-library and toolchain inventories are
checked at open/resume and full closure validation. Do not rebuild or replace
the installed base environment during a running campaign.

The generated module directory must be separate from base compiled/search
roots. `Formalization` is reserved as a generated **module** prefix: base
libraries must not import campaign modules. This keeps hidden indirect imports
from turning the output directory into an untracked proof dependency.

## Large-project organization

`project.sqlite3` is the transactional task/dependency ledger. Content-addressed
blobs hold transcripts; `sources/` holds indexed originals; `modules/` holds
separately compiled immutable modules; `proof_runs/` contains Mini attempt dossiers.
Dependency pages and source retrieval keep working prompts independent of total
project history. Wide import sets are represented by compiled import bundles,
without dropping prerequisites or concatenating their definitions into prompts.

Explicit retrievals remain in a persistent working-evidence notebook across
steps and restarts. Repeating a read refreshes its entry; the model may explicitly
release entries from its active context without deleting originals or archived
observations. The reviewer has its own notebook, and accepted review evidence is
preserved with the frozen statement and delivered to Mini. Context overflow
pauses the run explicitly; it does not silently shorten the evidence or plan.

Project-level completed work resumes. Within a failed individual Mini proof,
operational mode can reuse and recheck cached verified helpers; this adapter does
not restore the full prior Mini search graph or failed-strategy state.
Once Mini finishes a proof, its complete source is checkpointed before module
admission. Restarting after an admission failure retries that exact saved source
without repeating proof search, provided its task generation, frozen contract,
and dependencies still match. Admission is still checked; repeated rejection
returns the task for repair rather than accepting the saved proof on trust.

## Export

```sh
.venv/bin/python -m ensemble_prover.formalization export runs/formalization/my_project \
  --output runs/formalization/my_project_export
```

Export requires a verified root, checks its exact theorem identity and dependency
closure, and re-imports the copied modules from an isolated bundle. Existing
destinations are never overwritten. The bundle includes separate Lean modules,
`Root.lean`, original documents, an environment record, and replay instructions.
It depends on the recorded Lake/Mathlib environment; it is not a vendored project.
`export.json` records both the current root objective and the initial objective,
so an explicit revision remains visible.

Follow the generated bundle's `README.md` to replay. Its command has this form:

```sh
cd /absolute/path/to/the/recorded/lake_project
LEAN_PATH=/absolute/path/to/my_project_export \
  lake env lean /absolute/path/to/my_project_export/Root.lean
```

Update the bundle paths if it is moved. This re-imports the exported compiled
module closure against the required base environment; it is not a fresh,
self-contained Lake dependency download or a rebuild of every exported source.

## Validation and limits

Tests cover a 30,000-task dependency graph, wide fan-in, competing processes,
lease expiry, cancellation, revision invalidation, large-source indexed reads,
exact plan delivery, independent review, real Lean module chains, and instance-
sensitive frozen statements. These test orchestration and trust boundaries.

On 2026-09-05, following three adversarial review passes, all 319 formalization
tests passed without skips in four nonoverlapping parallel selections. Combined
Python line coverage of `ensemble_prover.formalization` was 91.09%. A separate
248-test compatibility selection covering theorem projects, the original NL
frontend, prompt support, and recursive helpers also passed, as did a 1,479-test
Mini finalization/session/transaction selection. These selections overlap and
are scoped measurements, not coverage of the entire prover repository.

The [adversarial review record](formalization-adversarial-review-20260905.md)
details the findings, regression evidence, and trust limits. Corrections cover
indirect compiled-import provenance, exact recursive context delivery, restart
state, proof-receipt/live-state rollback, and terminal provider failure handling.
They preserve generic universes and genuine verified completion authority;
they do not relax proof admission.

The scripted CostTree end-to-end test uses real Lean and Mini execution to
construct definitions, prove three supporting lemmas and a final theorem,
resume after reopening the project, and export nine modules. Its source includes
a searchable two-megabyte appendix; model responses are scripted, so this is an
integration/retrieval test, not a measure of model mathematical ability.

The live `finite_differences.md` evaluation used OpenAI-routed `gpt-5.6-terra`
for formalization/review and `gpt-5.6-luna` for proof search. It produced and
verified the definitions, pairwise commutation lemma, and list-induction theorem
for arbitrary abelian groups, then exported and checked five modules. This
development run was resumed across bug fixes, with an already-generated proof
replayed unchanged; it is not a clean unattended success-rate measurement or a
frontier-mathematics benchmark. Its input and the CostTree fixture are provided
in `examples/formalization/`.

Million-line Lean compilation, months-long autonomous operation, and frontier
research-level success rates have not been established. Kernel checking alone
cannot detect a mistranslated mathematical problem. Large developments still
depend on model capability, useful decomposition, suitable libraries, and
independent mathematical review of the resulting formal statements.
