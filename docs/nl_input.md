# Natural-language input (experimental)

The `ensemble_prover.nl_input` module translates a text or LaTeX mathematical
claim to Lean definitions and a proposition, checks them with Lean, and starts Mini Prover.
It is included in release 1.07; older Mini-only releases do not include it.
Run the commands below from the repository
root containing `.venv/`, not from inside the `ensemble_prover/` package.

For resumable, multi-file development with independent model review, use the
[formalization campaign](formalization-campaign.md). For setup and a comparison
of input workflows, start with the [User Guide](USER_GUIDE.md#1-what-you-supply).

Use the same Python environment and API-key environment variables as Mini
Prover. Supply an existing, built Lake project with Mathlib available. Replace
`lean_project` below with its path; no Lean project is bundled with the release.

```bash
.venv/bin/python -m ensemble_prover.nl_input \
  --text 'For every natural number n, n + 0 = n.' \
  --project-path lean_project \
  -- --prover openai --prover-model gpt-5.6-luna
```

The formalizer defaults to `gpt-5.6-terra` through the OpenAI API. Proving uses
Mini Prover's existing defaults. Configure these roles separately:

```bash
.venv/bin/python -m ensemble_prover.nl_input \
  --text-file my_claim.txt \
  --project-path lean_project \
  --formalizer openai --formalizer-model gpt-5.6-terra \
  -- --prover deepseek --prover-model deepseek-v4-flash
```

Arguments after `--` go to Mini Prover. Input-selection and environment options
cannot replace the generated theorem. All normal proof budgets and model
options remain available through that handoff.

To translate and inspect without starting a proof search:

```bash
.venv/bin/python -m ensemble_prover.nl_input \
  --text 'The square of every real number is nonnegative.' \
  --project-path lean_project \
  --formalize-only
```

## Project context and new mathematical objects

The frontend is not restricted to claims already expressible using Mathlib's
existing definitions. The formalizer can introduce `def`, `abbrev`, `structure`,
`inductive`, `class`, and `instance` declarations in dependency order. These
must have complete direct-term bodies: generated axioms, placeholders, tactics,
attributes and compiler evaluation are rejected. The root proof is left to Mini.

Supply existing research definitions, notation and background results as trusted
Lean source; import project libraries by module name:

```bash
.venv/bin/python -m ensemble_prover.nl_input \
  --text-file research_claim.txt \
  --context-file ResearchContext.lean \
  --import MyProject.Background \
  --project-path /path/to/research-project \
  --formalizer-timeout-s 1800 --lean-timeout-s 600 \
  --formalize-only
```

`--import` is repeatable. Imported libraries supply Lean names; their complete
source is not automatically retrieved into the formalizer prompt. Include the
relevant mathematical meaning in the problem text or context file. Context is
checked before a model request, and its full source is retained in the artifact
and downstream proving context. Treat the project and context file as trusted
code: the generated-source checks are not an operating-system sandbox.

To prove an unchanged saved translation without another formalizer request:

```bash
.venv/bin/python -m ensemble_prover.nl_input \
  --prove-existing runs/nl_input/YOUR_RUN \
  -- --prover deepseek --prover-model deepseek-v4-flash
```

Reuse checks artifact hashes and the original project path, then Mini rechecks
the theorem in the current project. Project files at that path are not frozen.
Changed source or inconsistent metadata is rejected. Submit a revised claim as
a new run; reuse is not an editor or a full proof-search checkpoint mechanism.

## What the module does

- Accepts one claim as `--text` (alias `--from-nl`) or a UTF-8 `--text-file`.
- Asks for complete supporting definitions and one proposition with explicit variables.
- Checks the response schema, generated declarations and their dependencies,
  and the actual emitted theorem file with Lean.
- Gives full Lean/JSON errors back to the formalizer for up to three total
  attempts, configurable with `--max-attempts`.
- Stops with a question when the formalizer identifies missing context or a
  material ambiguity. Answer by submitting a revised, self-contained problem.
- Passes the original problem text and saved theorem to Mini Prover.

This is infrastructure for research-level claims and conjectures, not evidence
that the formalizer can autonomously formalize arbitrary frontier mathematics.
It does not yet construct a multi-file theory through a separate iterative
definition/proof-development loop, ingest diagrams or papers directly, or
discover an unstated answer. Mini's existing proof graph handles supporting
proof obligations after the definitions and root statement are admitted.

Lean checks the proposition's type and, later, the proof. Translation fidelity
is not certified: the module labels it `machine_proposed` and prints the
generated statement. There is no separate semantic critic in this first version.

## Saved files

Each run gets a new directory under `runs/nl_input`. `--output-dir` selects an
explicit directory, which must not already exist.

| File | Contents |
|---|---|
| `problem.txt` | Original UTF-8 input, including whitespace and line endings |
| `formalization.json` | Status, source hash, model, complete prompts, returned content, parsed provider responses and Lean errors |
| `context.lean` | Exact supplied context, when provided |
| `Problem.lean` | Context, generated definitions and checked proposition with a `sorry` proof slot for Mini to fill |
| `prover_command.json` | Argument list for the normal Mini Prover handoff |

The source text and model outputs are not silently shortened. If required
context exceeds the model's capacity, the transport raises an error. A
truncated, refused or incomplete response is saved and rejected. The module uses Mini's existing
model output limits without imposing a smaller formalization cap.
The original problem, formal signature and complete Lean preamble are marked
required in downstream prover/refiner prompts, including after compaction.
Existing description loading normalizes outer whitespace; exact original bytes
remain in `problem.txt`.

`--formalizer-timeout-s` bounds each formalizer operation including retries;
without it the selected provider's existing defaults apply. `--lean-timeout-s`
defaults to 300 seconds per check. Neither option limits output length.

`Problem.lean` is an input template, not a solved proof. Mini's normal run
directory, verification and solved-export process own the proof result. An exit
code of zero with `--formalize-only` means the translation passed Lean type
checking; it does not mean the theorem was proved.

The transcript preserves the response content and parsed provider payload
available through the shared client, not raw HTTP wire bytes. It contains the
submitted mathematical text and should be treated as private if the input is
private.

## Testing

The following commands are for the development repository. Tests and its
local `lean_project` fixture are not part of the public runtime distribution.

```bash
.venv/bin/python -m pytest -q tests/test_nl_input.py tests/test_nl_lean.py \
  tests/test_nl_artifacts.py tests/test_nl_context_handoff.py tests/test_nl_cli.py
```

Most tests use deterministic fake model responses. The real Lean test uses the
local `lean_project` Mathlib build and skips if that build is unavailable. Tests
do not call a paid model API.
