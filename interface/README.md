# Local browser interface

The interface starts English or Lean proof attempts, shows recorded progress
and translation results, and sends one confirmed cooperative interrupt to an
owned attempt. A verified export is the proof certificate. A translated
statement, accepted helper, or internally solved root does not certify the
original problem.

The release includes the browser source, the local API service, and its shared
run and launch support. Build the browser assets locally before starting the
service; Node.js is needed for installation and rebuilding, not while serving
the built page.

## Setup

Use Linux, standard CPython 3.11 or 3.12, and Node.js 22.20+ (22.x),
24.12+ (24.x), or 26+. From the repository root, create a virtual environment if one does not already exist, then install
the service dependencies and build the browser page:

```bash
python3.11 -m venv .venv
.venv/bin/python -m pip install -r requirements-interface.txt
.venv/bin/python -m pip check
npm --prefix interface/web ci
npm --prefix interface/web run build
.venv/bin/python -m interface.service
```

Use `python3.12` instead of `python3.11` if that is your installed supported
runtime. This installation includes the core prover dependencies; the browser
service remains optional for CLI users.

Open `http://127.0.0.1:8765`. This mode reads attempts without permitting
launch or stop. Starting the service without a built page prints the required
build commands and exits. Rebuild the page after changing its source.

The existing prover prerequisites still apply when starting work: a compatible
built Lake project, Lean and Lake on the service's PATH, and credentials or
subscription sign-in for the selected provider. The service inherits the
environment in which it starts. Export provider variables in that shell, or
use the selected subscription CLI's existing sign-in. The service does not
load `.env` into its provider discovery environment. Provider secrets belong
in the service environment, not in browser forms.

## Starting and reading attempts

The **Launcher** accepts English or LaTeX directly, or lets you choose a Lake
project, Lean file, and theorem from discovered lists. Use **Browse folders**
for a project elsewhere on the machine. Recent projects and nearby projects
are discovered automatically; a linked worktree also finds projects in its
primary checkout. File and declaration lists are bounded and indicate when
they are incomplete. Discovery reads metadata without running Lean.

Choose a prover and, optionally, a separate refiner. Provider availability
reports installed tools or environment variables; it does not authenticate
an account. CLI providers can keep their default model. Search, reasoning,
and budget controls send only explicit overrides, including zero values.
The configuration panel shows the choices that will be submitted. **Setup**
stores project and prover defaults in this browser.

The launch checklist identifies missing choices and links directly to the
fields that need attention. Complete inputs do not establish that credentials
or the Lake toolchain will work. Translation-only ignores proof-search settings.
Unfinished numeric settings remain visible and block proof-search submission
until corrected; deliberately blank settings use the CLI defaults.
Relative project paths entered manually resolve against the service's
configured repository in both English and Lean modes.

**Progress** opens the most recent active or recorded run. Select a graph node
to inspect its status, recorded support relationships, and receipt time.
The **Formal mathematics** panel shows its recorded Lean statement. Expand
**Recorded Lean proof source** to read an available proof. Helper proofs must
match the recorded statement identity and verification environment; conflicting,
incomplete, or oversized records show an explanation instead of an inferred proof.
The displayed source does not change the root or export status.
**Graph & evidence** adds a node search and the retained event log. Milestones
open recorded receipts; the graph continues to show current recorded state,
so selecting a milestone does not reconstruct a historical graph.

Progress and Results show the time of their last successful read. A read
failure keeps previously received evidence visible and offers an immediate
retry. **Pause updates** freezes automatic refresh and sweep following while
the prover keeps working. **Refresh now** reads the selected attempt without
resuming automatic following; **Resume updates** restores automatic reads.
The retained event log can be searched by text and filtered by scope. Its
search covers the displayed recent events, not the complete run history.

For a sequential sweep, **Follow sweep** advances to the next recorded problem
or retry within that sweep. Other sweeps cannot change this selection.
Following uses sweep order rather than file modification times. Selecting a
run manually pauses following so completed results remain available for
inspection; check **Follow sweep** to resume. The follow setting is included
in the page URL, so separate tabs can follow separate sweeps.

**Results** searches recorded attempts and separates root outcomes, process
status, and export status. Filter by sweep or outcome, restrict to running
owned launches, or change the sort order to review a group of attempts.
Filters are included in the page URL and remembered in the current tab when
opening a run and returning to Results. Counts describe loaded attempts;
the library includes at most the latest 500 attempts and is not a complete
sweep scorecard. **No solve reported** includes active, translated, and
incomplete attempts without a recorded solve or export result; it does not
assert that their unread proof traces contain no progress.
Helpers and internal solves do not establish a
verified root export. Event text matches in the inspector may include other
scopes or similarly named helpers and are labeled accordingly.

Enable launch and cooperative stop explicitly:

```bash
.venv/bin/python -m interface.service --control
```

For different storage locations or an occupied port:

```bash
.venv/bin/python -m interface.service --control \
  --run-root /path/to/runs \
  --state-root /path/to/interface-state \
  --repo-root /path/to/this-checkout \
  --port 8999
```

Use the same state directory when reopening the library. It records launches,
including translations that have no proof-search trace. Formalization files
live in its `nl/` directory and their statement, status, and Lean source are
shown in the attempt view. Generated Lean source is shown as text; the page
does not execute it. Failed launches and unsuccessful translations remain
visible with their actual status.

Without `--run-root`, the service uses the checkout's `runs/mini_prover`
directory, or the primary checkout's existing runs when started in a linked
worktree. An explicit `--run-root` always takes precedence.

Translation-only does not require prover settings. It uses the natural-language
formalizer's own defaults; see [natural-language input](../docs/nl_input.md)
for those defaults and the CLI options for changing them. Notes-to-project
and open-ended research are not available in this interface.

A start keeps its submission identity through an uncertain response so a retry
can return the existing launch. Each tab retains its unresolved submissions,
including earlier drafts, across reloads while session storage remains available.
Closing the tab or clearing browser data can discard those identities; check
the library before starting the same work in a new tab. Closing the page does
not stop an attempt. A launch response arriving after leaving the Launcher
does not change the page being viewed; the started attempt remains in Results.
Browsers that block local storage can still render the interface. Starting
work requires functioning session storage to retain its submission identity.
A cooperative interrupt
requests a stop; it does not claim that the process has already exited.
If saved launch state cannot be read reliably, control requests are refused and
the existing state file is preserved. Keep that state when investigating; a new
state directory cannot recover the previous launch and stop identities.

## Local request access

The service listens only on `127.0.0.1`. It accepts the configured port on
`127.0.0.1` or `localhost` as its HTTP host, checks browser origins and fetch
metadata, and requires a per-service capability on mutations. The page obtains
that capability from `/api/session` and holds it in memory. Restarting the
service changes it. API responses are not cached and the page cannot be framed.

Mutation bodies must be JSON and at most 64 KiB. Requests with excessive JSON
nesting or structure are rejected. These boundaries assume trusted local
users, a trusted run directory, and a trusted service state directory. Do not
publish the port through a network proxy.

## Browser development

Start the API from the repository root:

```bash
.venv/bin/python -m interface.service --api-only --control \
  --web-origin http://127.0.0.1:5173
```

In another terminal:

```bash
npm --prefix interface/web run dev
```

Open `http://127.0.0.1:5173`. Its `/api` proxy targets the service on port 8765.
Use the exact configured hostname. Trusting the development origin is explicit;
it is unnecessary when the Python service serves the built page itself.

For a built-page preview, use `npm --prefix interface/web run preview` and
start the API with `--web-origin http://127.0.0.1:4173` instead. The build script is in `interface/web/package.json`.
