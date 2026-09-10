# Research claim ledger

Last updated: 2026-09-10.

This package implements durable claims, evidence, independent review, and bounded
assignments for coordinated mathematical research.
It records which necessary implication a result supplies and whether its
quantitative losses are acceptable. An experimental executable loop adds
model-backed investigations, fresh reviews, isolated experiments, durable shared
request admission, and exact formalization handoffs. See
[Autonomous mathematical research](DISCOVERY.md) for use and limitations.

The maintained prover enters through `mini_prover` and `mini_session.factory`
into `MiniSession`; its formal search state and Lean acceptance remain separate.
The existing `formalization` campaign handles source-grounded decomposition,
semantic review, and compiler admission. This ledger adds written research
provenance alongside those systems. Formalization execution remains separately
authorized; the research loop does not grant proof-acceptance authority.

| Module | Responsibility |
| --- | --- |
| [model.py](model.py) | Exact contracts, quantitative costs, obligations, input validation |
| [store.py](store.py) | SQLite persistence, revisions, artifact bytes, evidence, reviews, contributions, operations, assignments |
| [scheduler.py](scheduler.py) | Explainable priorities and bounded assignment context |
| [cli.py](cli.py) | JSON submissions and reports through `python -m` |
| [discovery.py](discovery.py) | Executable research programs, reviews, and exact handoffs |
| [discovery_store.py](discovery_store.py) | Durable admission, response recovery, atomic application |
| [experiments.py](experiments.py) | Optional isolated, bounded Python computations |

## Three separate assessments

`show` returns a claim specification, its current revision, `assessment`, and
research `progress`. Statuses are derived from records; they are not writable
fields in a claim specification.

| Assessment | Meaning |
| --- | --- |
| Correctness | `proposed`, `supported`, `refuted`, or `unresolved`, based on revision-bound arguments, counterexamples, reviews, and dependency obligations |
| Verification | Separate written proofs, independent reviews, exact computations, primary sources, reported kernel artifacts, counterexamples, and gaps |
| Contribution | A reviewer records `closes`, `improves_bound`, `eliminates_route`, `irrelevant`, or `unresolved` for a particular parent obligation |

Support requires an independent review of a `written_proof`; refutation requires
an independent review of a `counterexample`. A claim with dependencies also needs
its obligations closed before it can be supported. Closing all helpers still
requires the parent's own reviewed written argument. Conflicting evidence,
unresolved reviews, and recorded gaps prevent an unqualified supported result.

An independent correctness reviewer must differ from both the claim author and
the reviewed evidence's author. Contribution reviewers must differ from the
supplier author. These are locally asserted identity strings, not authenticated
proof that two different people or model instances performed the work.

Imported `kernel_report` evidence is historical metadata. It does not rerun
Lean, authenticate a report, or establish that its theorem matches this claim.
`verification.kernel_verified` is always `false`; scheduler `root_proved` is also
always `false`. Finite computations and source records alone do not establish a
general claim.

Each dependency contains an `obligation_id`, a `supplier_id`, the exact required
`contract`, and optional `quantitative_requirements`. Closure requires all of:

- A currently supported supplier and a current contribution review.
- Identical statement and domain strings, and identical ordered quantifier
  arrays. The supplier's hypothesis strings must form a subset of the required
  hypothesis strings; extra assumptions are rejected.
- A nonempty offered cost for every nonempty required cost field, and the
  reviewer's explicit `costs_acceptable: true`.

These checks are conservative syntactic checks. They do not prove equivalence
of prose or evaluate inequalities such as `log N >= N^0.1`. Reviewers must check
the structures, conventions, exceptional cases, parameter dependence, and
quantitative losses relevant to their problem. Different
wording or a legitimate domain transfer needs an explicit bridge claim.
`improves_bound` can record useful partial progress without closing an obligation.
It requires an actual quantitative requirement, recorded relevant costs, and
compatible domain, hypotheses, and quantifiers. Its conclusion may express a
weaker bound; the reviewer must explain the improvement.

## Run a complete local example

Run these Bash commands from the Git repository root, the directory containing
`ensemble_prover/` and `.venv/`. This manual ledger example uses Python's standard library and
needs no model provider or Lean process.

```bash
.venv/bin/python -m ensemble_prover.research_claims --help
research() { .venv/bin/python -m ensemble_prover.research_claims "$@"; }
RESEARCH_DEMO=$(mktemp -d)
research init "$RESEARCH_DEMO/ledger"
```

The following toy helper has a complete elementary proof. Its retained domain
has only `ceil(log N)` points, while the proposed iteration needs at least
`N^0.1` points. It demonstrates a correct result that fails the target's
quantitative requirement; it makes no claim about solving a conjecture.

```bash
cat > "$RESEARCH_DEMO/helper.json" <<'JSON'
{
  "claim_id": "density_helper",
  "author": "alice",
  "contract": {
    "statement": "Deleting H increases the relative density of A.",
    "domain": "finite subsets of the integers",
    "hypotheses": ["N >= 16", "A is nonempty", "A is contained in [N] minus H", "|[N] minus H| = ceil(log N)"],
    "quantifiers": ["for every integer N", "for every A,H subset of [N]"]
  },
  "quantitative_costs": {"domain_size": "ceil(log N)"},
  "remaining_gap": "The retained set need not support useful iteration."
}
JSON
cat > "$RESEARCH_DEMO/target.json" <<'JSON'
{
  "claim_id": "iteration_target",
  "author": "coordinator",
  "contract": {
    "statement": "A density increment is available on a domain large enough for the proposed iteration.",
    "domain": "finite subsets of the integers"
  },
  "dependencies": [{
    "obligation_id": "large_domain_increment",
    "supplier_id": "density_helper",
    "contract": {
      "statement": "Deleting H increases the relative density of A.",
      "domain": "finite subsets of the integers",
      "hypotheses": ["N >= 16", "A is nonempty", "A is contained in [N] minus H", "|[N] minus H| = ceil(log N)"],
      "quantifiers": ["for every integer N", "for every A,H subset of [N]"]
    },
    "quantitative_requirements": {"domain_size": "at least N^0.1 for all sufficiently large N"}
  }]
}
JSON
research add-claim "$RESEARCH_DEMO/ledger" --file "$RESEARCH_DEMO/helper.json"
research add-claim "$RESEARCH_DEMO/ledger" --file "$RESEARCH_DEMO/target.json"
```

Create suppliers before their parents. Unknown references, dependency cycles,
and supersession cycles are rejected. A contract preserves the original string
content; rewriting mathematically significant text is a revision.

Snapshot the complete proof, then attach evidence and an independent review.
The sample review below is an illustrative local assertion; an actual research
run should record a review that was performed.

```bash
cat > "$RESEARCH_DEMO/proof.md" <<'PROOF'
Let [N] = {1,...,N}, and let log denote the natural logarithm.
Set m = ceil(log N). For N >= 16, 0 < m < N.
By the hypotheses, A is a nonempty subset of [N] minus H, whose size is m.
Its original relative density is |A|/N; after deleting H it is |A|/m.
Since |A| > 0 and m < N, the latter is strictly greater.
This proves the exact helper. The argument uses arbitrary holes and does
not show that the retained set is an interval or arithmetic progression.
Moreover, m/N^0.1 tends to zero, so this domain size fails the stated
asymptotic iteration requirement.
PROOF
RESEARCH_ARTIFACT=$(research add-artifact "$RESEARCH_DEMO/ledger" --file "$RESEARCH_DEMO/proof.md" |
  .venv/bin/python -c 'import json,sys; print(json.load(sys.stdin)["artifact_id"])')
cat > "$RESEARCH_DEMO/evidence.json" <<JSON
{
  "claim_id": "density_helper", "expected_revision": 1,
  "kind": "written_proof", "author": "alice",
  "artifact_ids": ["$RESEARCH_ARTIFACT"],
  "details": {"scope": "The exact finite-set contract", "derivation": "Complete proof in the attached artifact."}
}
JSON
RESEARCH_EVIDENCE=$(research add-evidence "$RESEARCH_DEMO/ledger" --file "$RESEARCH_DEMO/evidence.json" |
  .venv/bin/python -c 'import json,sys; print(json.load(sys.stdin)["evidence_id"])')
cat > "$RESEARCH_DEMO/review.json" <<JSON
{
  "claim_id": "density_helper", "expected_revision": 1,
  "evidence_id": "$RESEARCH_EVIDENCE", "reviewer": "bob",
  "verdict": "supported",
  "rationale": "The complete derivation follows from cardinalities and m < N. It establishes only the stated density comparison."
}
JSON
research add-review "$RESEARCH_DEMO/ledger" --file "$RESEARCH_DEMO/review.json"
cat > "$RESEARCH_DEMO/contribution.json" <<'JSON'
{
  "parent_id": "iteration_target", "expected_revision": 1,
  "obligation_id": "large_domain_increment", "expected_supplier_revision": 1,
  "reviewer": "carol", "decision": "irrelevant", "costs_acceptable": false,
  "rationale": "ceil(log N)/N^0.1 tends to zero. This helper does not supply the domain size required for iteration."
}
JSON
research assess-obligation "$RESEARCH_DEMO/ledger" --file "$RESEARCH_DEMO/contribution.json"
research show "$RESEARCH_DEMO/ledger" density_helper
research show "$RESEARCH_DEMO/ledger" iteration_target
research frontier "$RESEARCH_DEMO/ledger" iteration_target
research export "$RESEARCH_DEMO/ledger" --output "$RESEARCH_DEMO/export.json"
research read-artifact "$RESEARCH_DEMO/ledger" "$RESEARCH_ARTIFACT" --output "$RESEARCH_DEMO/restored-proof.md"
```

The helper is `supported` with `kernel_verified: false`. The target retains its
obligation, and its closed-obligation count stays zero. The JSON export includes
records and a top-level artifact metadata list with hashes. Saved assignment
packets also appear in exports and may contain complete UTF-8 or base64 artifact
contents. `read-artifact` restores individual stored artifacts. Export and
restored-file destinations must not already exist.

## Revise claims and preserve failed routes

`revise-claim` accepts a complete replacement specification with the same
`claim_id`. It requires the expected current revision. Revision numbers begin at
one; a revision increments the changed claim and every claim that transitively
depends on it, even when a dependent specification's text stays the same.
Previous evidence, reviews, contribution assessments, and operations remain in
`history` but do not silently attach to a new revision.

```bash
.venv/bin/python - "$RESEARCH_DEMO" <<'PY'
import json
import pathlib
import sys

directory = pathlib.Path(sys.argv[1])
claim = json.loads((directory / "helper.json").read_text())
claim["remaining_gap"] = "Need a domain of size at least N^0.1; arbitrary holes do not provide it."
(directory / "helper-v2.json").write_text(json.dumps(claim))
PY
research revise-claim "$RESEARCH_DEMO/ledger" density_helper --expected-revision 1 --file "$RESEARCH_DEMO/helper-v2.json"
research history "$RESEARCH_DEMO/ledger" density_helper
research show "$RESEARCH_DEMO/ledger" iteration_target
```

Both claims now have revision two. New evidence and reviews must name their
current revision; contribution submissions must also name the current supplier
revision. Stale submissions fail. New supplier evidence or reviews can also make
earlier contribution assessments inactive without changing the statement; check
`show` before publishing follow-on work.

To record a failed route, attach a `counterexample` artifact and supply
`details.hypotheses_check` and `details.conclusion_violation`. An independent
`refuted` review establishes the recorded refutation. A separate
`eliminates_route` contribution can then mark the proposed implication unusable.
The parent's necessary obligation stays open. A `gap` artifact records a precise
obstruction without claiming a counterexample. Replacement claims may use
`supersedes` to reference older claims; their evidence and corrected
interpretations remain available in history and assignment context.

## Resolve review disagreements without rewriting mathematics

An incorrect objection does not require changing a correct theorem statement.
Submit an independent `add-review` with `verdict: "dismissed"` for the invalid
evidence, explaining the error in `rationale`. Dismissal rejects that particular
argument or objection; it neither proves nor refutes the claim. Other objections
remain active, and support still requires a reviewed written proof.

To replace earlier reviews of that evidence, include
`supersedes_review_ids: ["review-..."]`. IDs must name active reviews of the same
evidence in the current claim revision. Conflicting reviews not explicitly
replaced remain unresolved, including any review published concurrently.
An already replaced ID causes a conflict instead of silently overwriting work.
The original evidence, artifact bytes, and review rationales remain in `history`.
`verification.active_review_ids` and `dismissed_evidence_ids` distinguish current
assessment inputs from that archive.

Contribution assessments also preserve disagreement. For a given obligation and
supplier state, differing decisions or cost acceptances produce an unresolved
aggregate. Repeating `closes` cannot erase `irrelevant` or `unresolved`.
`assessment.contributions` reports `conflicted` and the contributing
`assessment_ids`; the original reviewers and rationales remain in history.

An explicit resolution uses the usual `assess-obligation` submission plus
`supersedes_contribution_ids` listing the assessments it replaces and
`expected_supplier_state_token` copied from the supplier's
`assessment.assessment_token` in `show`. Both the current supplier revision and
state must match. The state token is optional for ordinary legacy submissions,
but workers should always include it: new evidence can make their review stale
without changing the statement. It is required when replacing assessments.
After an evidence dismissal changes supplier state, re-review its contribution;
old parent closures do not automatically reactivate.

## Prepare and finish bounded assignments

`frontier` explains priorities in terms of missing implications, counterexample
searches, consequential bounds, and independent reviews. Progress counts active
contributions to currently relevant obligations, with immediate and transitive
counts reported separately. Correct but irrelevant helpers do not count as
closed obligations; eliminated routes still leave necessary implications open.

When the target itself is refuted, its old helper obligations remain available
for inspection but no longer count as current progress. The frontier requests
independent review of the refutation. New assignments are restricted to that
review until an explicit target revision, replacement, or dismissal of its
current-revision counterexample reviews resumes research.
Automatic revisions caused by a helper change preserve this scheduling hold:
`historical_refutations` identifies the older reviews and
`requires_target_revision` remains true. Those older reviews do not become
current-revision mathematical evidence. A held supplier cannot receive positive
contribution credit, and its frontier requests independent review as well.
Conflicting evidence can change correctness to `unresolved`, but cannot erase a
recorded counterexample review. An explicit superseding review can dismiss a
mistaken current-revision refutation; older refutations from an automatically
invalidated revision still require explicit reconsideration of the claim.
Assignments cannot descend through a held or discarded route. A sublemma remains
assignable when another currently relevant dependency path reaches it. The
boundary supplier itself remains available for review or replacement work,
subject to its refutation hold.

`assign` supports `investigate`, `counterexample`, `quantitative_bound`, and
`independent_review`. It snapshots the target, subject, dependency revisions,
required checks, prior evidence and failed routes, quantitative requirements,
question, worker identity, output ownership, and step/time bounds. Workers may
return a positive argument, a counterexample, or a precise gap. Review
assignments require a worker who authored neither the subject claim nor its
recorded evidence.
Default checks are domain-neutral. Supply an optional `additional_checks` array
for the subject's particular hazards (for example characteristic assumptions,
geometric degeneracies, or Fourier normalization). These supplement the defaults
and are retained verbatim; they do not revise the mathematical claim.
Assignment publication checks both claim revisions and evidence/history tokens.
If evidence, a contribution, or a prior assignment's lifecycle changes while the
packet is prepared, publication fails without reserving the assignment ID or
output; retry with fresh context. Prior assignments in each claim's packet
history retain their questions, identities, bounds, output paths, and lifecycle
metadata. Graph-wide arrays and nested context are available through the original
archived packet's assignment ID, rather than repeated for every claim.

External JSON and Python metadata are limited to 64 nested objects or arrays.
Internal assignment admission allows 128 levels and serialization allows 256,
leaving room for report envelopes. Custom packet metadata retained in future
assignment histories must satisfy the external 64-level bound. Mathematical text
and artifact contents are not truncated. Excessive nesting is rejected before mutation; legacy records
that exceed Python's recursion limit produce a controlled CLI error.

```bash
cat > "$RESEARCH_DEMO/assignment.json" <<'JSON'
{
  "target_id": "iteration_target", "claim_id": "density_helper",
  "assignment_id": "round1_extraction", "round_id": "round1",
  "worker": "extraction_researcher", "work_kind": "investigate",
  "question": "Which additional hypothesis could preserve at least N^0.1 points after a density increment? Return a precise gap if none is justified.",
  "owned_output": "research-output/round1-extraction.md",
  "max_steps": 10, "max_seconds": 300,
  "additional_checks": ["Check that the retained domain preserves integer positions and arithmetic progressions."]
}
JSON
research assign "$RESEARCH_DEMO/ledger" --file "$RESEARCH_DEMO/assignment.json"
cat > "$RESEARCH_DEMO/finish.json" <<'JSON'
{
  "assignment_id": "round1_extraction", "outcome": "provider_failure",
  "details": {"message": "Illustrative operational failure: no worker response was received."}
}
JSON
research finish-assignment "$RESEARCH_DEMO/ledger" --file "$RESEARCH_DEMO/finish.json"
research assignments "$RESEARCH_DEMO/ledger"
```

This persists a work packet and its outcome; it does not launch a worker, execute
commands, enforce runtime budgets, or create the owned output file. A coordinator
must dispatch and supervise work externally. Assignment IDs are unique; duplicate
questions in the same round and conflicting pending output ownership are rejected.
Output paths may be relative or absolute and are recorded as canonical absolute
paths, resolving relative paths from the command's working directory.
Completing an assignment does not publish evidence automatically.

Operational outcomes are `completed`, `timeout`, `provider_failure`,
`tool_unavailable`, and `cancelled`. They supply no mathematical evidence.
`record-operation` accepts a JSON object containing `claim_id`,
`expected_revision`, `outcome`, and `details` when an outcome needs to be attached
directly to a claim. A provider failure therefore never refutes a claim.

## Evidence, persistence, and validation

All evidence requires at least one previously stored artifact. `add-artifact`
stores complete bytes under a SHA-256 identifier; reading verifies the hash.
Store complete derivations, source excerpts and exact locations, experiment
scripts, outputs, and reproduction instructions instead of only conclusions.

Evidence kinds are `written_proof`, `counterexample`, `exact_computation`,
`primary_source`, `kernel_report`, and `gap`. An `exact_computation` submission
requires `details.scope`, a `details.command` argument array, a nonempty
`details.environment` object, and an integer `details.exit_code`. These record a
reported experiment; the ledger does not execute or independently verify it.
Use artifacts for complete source and output bytes. A `primary_source` submission
can record bibliographic details and exact source locations in `details`.

The ledger uses schema version **4**, stored in `DIRECTORY/ledger.sqlite3`.
Use a dedicated directory. Existing prover or campaign databases are not migrated.
Version 1, 2, and 3 research ledgers require an explicit upgrade:

```bash
.venv/bin/python -m ensemble_prover.research_claims upgrade DIRECTORY
```

Back up the ledger before upgrading, and stop older ledger clients first.
The upgrade validates the known legacy schema, retains all records and
artifact bytes, and adds discovery runtime tables where absent. Version 4 adds
durable child-result continuation semantics without reallocating existing run
budgets. Version 1 upgrades also enable
conflict-aware interpretation. Previously hidden
contribution disagreements or changed assessment tokens may therefore reopen
obligations; re-review affected contributions. Older code rejects
version 4 when opening a ledger; the upgrade cannot revoke already-open legacy
connections, so mixed-version operation is unsupported. Unknown schemas and versions are
rejected without alteration; no downgrade is provided.
Mutations use transactions, revision checks occur while holding the write lock,
and composite reports read one consistent database snapshot. JSON inputs reject
unknown top-level fields, duplicate keys, and nonfinite numbers. CLI submission
objects must include every field shown in the relevant example, including
`details`, `artifact_ids`, and explicit cost acceptance where applicable.

From the Git repository root:

```bash
.venv/bin/python -m pytest ensemble_prover/research_claims/tests
```

These tests are included in the repository's normal pytest discovery and
excluded from runtime release snapshots, together with internal review and
validation reports.

See [IMPLEMENTATION.md](IMPLEMENTATION.md) for the implementation boundary and
follow-on work. Tests cover local workflows and the ledger's admission rules;
they do not prove submitted mathematics.
