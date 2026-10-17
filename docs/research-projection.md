# Inspecting retained research

The research projection command connects retained proof helpers, graph records,
research questions, and attempts in an authorized offline view. It saves the
selected values in a separate sidecar, so a reference continues to identify the
same evidence after the source changes. Explicit advisory associations let an
operator record possible relevance, unresolved questions, and scoped objections.

Run the command from your installed Ensemble Prover environment:

```sh
python -m ensemble_prover.research_projection --help
```

## Configure sources and visibility

Prepare independent, quiescent copies or consistent exports of the sources you
are authorized to inspect. A proof source is an exact committed checkpoint JSON;
retain its page objects when the checkpoint uses external pages. A research
source is a directory containing `ledger.sqlite3`, or that file itself. Copying
the main file of a running SQLite WAL database does not produce a consistent
export. The reader rejects adjacent WAL, SHM, or journal files and does not open
live owners, initialize missing ledgers, or create missing subjects. Research
exports must use a supported owner schema; computed and virtual layouts are
rejected before record queries run.

Create a private host policy file, for example `/srv/ensemble/projection-policy.json`:

```json
{
  "format_version": 1,
  "sidecar": "/srv/ensemble/inspection/research-views",
  "sources": {
    "proof": {
      "path": "/srv/ensemble/source-copies/attempt/checkpoints/000000000170.json",
      "namespace": "proof-attempt"
    },
    "research": {
      "path": "/srv/ensemble/source-copies/research/ledger.sqlite3",
      "namespace": "research-ledger"
    }
  },
  "source_roots": ["/srv/ensemble/source-copies", "/srv/ensemble/prover/runs"],
  "scanner_roots": ["/srv/ensemble/prover/mathematical-memory"],
  "scope": "my-research-inspection",
  "redactions": [],
  "max_storage_bytes": 536870912,
  "max_source_bytes": 67108864,
  "timeout_seconds": 10
}
```

```sh
chmod 600 /srv/ensemble/projection-policy.json
```

List all canonical run, checkpoint, artifact, ledger, and mathematical-memory
roots, including every configured recursive scanner root. The sidecar must be
outside these trees. Its directories and their ancestors must prevent unrelated
users from replacing files. Overlap, symlink aliases, and hardlinked sidecar
files are rejected. The host policy belongs to the current operating-system
user; command input cannot choose another principal or grant itself access.

Either source may be omitted. Missing, unsupported, or oversized source
components appear in coverage. Source namespaces are stable identities chosen
by the host; keep their meaning consistent across copies. `redactions` contains
literal strings to hide in every output. Embedded hosts can provide a
`HostPolicy` that checks current source, caller, audience, and answer visibility.
Changing visibility can invalidate an earlier view or page. A policy that would
change an exact reference identity causes that view to be refused. Hidden records
and records requiring their undisclosed prerequisites are omitted as whole records.
Hiding a child job preserves its public parent claim and independent sibling jobs.
Known record references retain their entity type and campaign scope when
filtering dependencies. A hidden assessment inside a research finding also hides
its corresponding indexed decision and dependent records.
Hidden conversation or session identity data cannot supply public statements or
context identifiers. Helpers and graph nodes with hidden contract fields are
omitted together with their references. Direct optional checker fields can be
removed; a hidden descendant inside other record metadata omits the whole record.
Removing a hidden target does not make
another target the unique active statement.

Library callers default to a public reader context and must explicitly request
operator access when authorized by their host. The local command uses the current
user's operator context. Retained views remain bound to their principal, role,
audience, answer visibility, and scope; changing that context requires a new view.

## Create, inspect, and resolve

```sh
python -m ensemble_prover.research_projection --config /srv/ensemble/projection-policy.json create --offline > view.json
python -m ensemble_prover.research_projection --config /srv/ensemble/projection-policy.json read view.json
python -m ensemble_prover.research_projection --config /srv/ensemble/projection-policy.json search view.json "estimate" --limit 20
python -m ensemble_prover.research_projection --config /srv/ensemble/projection-policy.json page view.json --path '["proof","sessions",0,"helpers"]' --length 6000 > page.json
python -m ensemble_prover.research_projection --config /srv/ensemble/projection-policy.json resolve page.json
```

Search returns exact record references and expansion paths, including complete
arguments pinned into that view. Results carry an unexpanded-contract marker;
use the page command to inspect all hypotheses and evidence before judging
applicability.

Paths are JSON lists of keys and nonnegative indexes, relative to the view's
`values`. Inspect `read` output to choose a path. `json-v1` preserves structured
values; `text-v1` selects a string. A page reports `next_start`; pass that value
as `--offset` with the same view, path, and transform to continue. The derived
reference includes the original view, selection, transform, range, policy
binding, and content digest. It is a sidecar reference, not a canonical artifact
identifier. Permission is checked again before returning any page.

Each view records separate proof and research acquisition identities and times.
It does not claim a joint transaction or complete past history. Helper references
retain exact source digests, assumptions, and available context; legacy short
hashes remain separate identifiers. Missing question-selection provenance stays
unknown. General source artifact bodies, removed earlier work, and unsupported
owner records may be absent; inspect coverage before interpreting the view.

Reads and page resolution do not create views or associations. There is no
automatic expiry. A storage ceiling accounts for filesystem allocation and
reserves transaction space; new writes are rejected when that space is unavailable.
Opening a sidecar can recover an interrupted SQLite transaction before reading
its retained data. Before each mutation, the sidecar durably records a digest of
its committed contents and advances that digest before acknowledging a successful
commit. Recovery validates synchronized journal records and checks that an isolated
rollback restores those contents before touching the live database. Unverifiable
recovery data is refused and retained for inspection. Older sidecars with a retained
journal but no recorded digest cannot be recovered automatically. Older sidecars
without a journal establish the digest before their next write.
Recovery scratch files stay outside declared source
and scanner roots, independently of `TMPDIR`. If no safe writable location is
available, recovery returns `observation_unavailable`.
Writers require DELETE journals with SQLite
[`EXTRA` synchronization](https://www.sqlite.org/pragma.html#pragma_synchronous),
including the directory synchronization after journal deletion. Durability
depends on the filesystem honoring those synchronization requests.

Explicit deletion invalidates that view and its pages:

```sh
python -m ensemble_prover.research_projection --config /srv/ensemble/projection-policy.json delete view.json
```

## Save advisory associations

Create a command JSON containing `command_id`, `proposals`, and optionally
`authoring_refs`. Qualify the command key as
`<view_ref.namespace>:command:<your-stable-key>`. Copy exact `view_ref` objects
from issued results into a proposal's `source` and `target`, or use an exact
`view_item` reference with a value path and digest. Include all inspected input
references in `authoring_refs`, including exact `page_ref` objects returned by
page inspection. Search-result references bind to the filtered record shown
when issued. Page inputs retain their parent-view restrictions and the
policy conditions of the selected transform and range. A partial page does not
establish a complete mathematical contract. For example, the proposal body is:

```json
{
  "kind": "may_help",
  "source": {"...": "exact issued reference"},
  "target": {"...": "exact issued reference"},
  "scope": {"assumptions": ["the original hypotheses"]},
  "prose": "Investigate whether the retained bound applies under these hypotheses.",
  "status": "proposed"
}
```

The ellipses above are placeholders; use complete reference objects. An optional
`argument` field stores exact text or structured JSON, including a complete
`{"connective":"AND","antecedents":[...]}` contract. Large arguments are
retained as sidecar objects with an unexpanded reference; premises are never
silently truncated into a sufficient subset.

```sh
python -m ensemble_prover.research_projection --config /srv/ensemble/projection-policy.json propose command.json
python -m ensemble_prover.research_projection --config /srv/ensemble/projection-policy.json relations --query bound
python -m ensemble_prover.research_projection --config /srv/ensemble/projection-policy.json relation relation-ref.json
python -m ensemble_prover.research_projection --config /srv/ensemble/projection-policy.json argument argument-ref.json
```

Updates specify `relation_id` and `expected_revision`. Identical command replay
returns the saved result; changed bodies under the same key conflict. Stale
revisions do not silently rebase. Commands accept at most 16 proposals and 16
inline references per proposal; structured inline metadata is bounded at 32 KiB.
Inspect each item outcome when a batch contains invalid proposals. Storage
failure returns an unsaved result with the command identity for retry.

Notes inherit their input restrictions transitively, including the exact caller
context of cited views. Complete authoring provenance does not remove those
restrictions. Local commands retain
notes in the author's private inspection scope because the command cannot
establish every source the operator has seen. Citation omission cannot make a
note public. Inputs that exceed the bounded policy dependency traversal are
rejected. An association never proves a claim, fills a dependency, changes a
hold, or authorizes spending. Recorded verification, current applicability, and
proposed relevance remain distinct. A checked `P → Q` still requires `P` to
obtain `Q`; a theorem about a scientific model does not certify that model's
physical applicability.

Saved notes with older, incomplete contextual policy witnesses return
`stale_policy`. Reauthor those notes from currently readable exact inputs using
a new command identity. Existing immutable references are not rewritten.
Withdrawal changes only a note's status. Its endpoints, kind, scope, text, and
evidence remain fixed even when an input is no longer available.

Legacy root/helper `decomposes_to` attachments display as inventory membership;
`supports` edges display as recorded dependencies unless the owner retained
stronger proof-use evidence. These display labels do not alter the graph. The
command does not enable live observation, change model context, register model
tools, or schedule work. Ordinary proof and research workflows retain their
existing persistence, admission, and accounting rules.
