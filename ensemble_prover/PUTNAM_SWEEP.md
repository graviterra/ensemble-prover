# Random unsolved Putnam sweep

From the repository root, run:

```bash
./scripts/sweep_putnam_unsolved.sh -- --prover openai --parallel-samples 2
```

Run `./scripts/setup_venv.sh` first if the repository's `.venv` is not installed.
The command above expects a separately supplied, compatible PutnamBench checkout
at `external/PutnamBench`, with its Lean/Lake dependencies ready. For a checkout
elsewhere, pass `--putnam-dir /path/to/PutnamBench/lean4/src` before `--` when
creating the sweep. The release does not include the benchmark or Lean project.

This attempts every currently unsolved PutnamBench problem once, in random order.
Previously failed attempts remain eligible unless an export now exists.
By default, the sweep excludes problems with an existing Putnam `.lean` export
in `runs/mini_prover/solved` or `runs/solved`, and checks again before each launch.
It counts each problem once across visible-answer and versioned filenames.
This is a scheduling choice: legacy exports and exports flagged by the axiom
audit are skipped too, and their verification/audit status remains unchanged.
Use `--solved-policy verified` before `--` to restrict exclusions to the existing
verified-manifest filter instead. That filter only recognizes matching verified
manifest entries, so exports missing from the current manifest remain eligible.
The queue size depends on your local corpus and solved exports.
Add `--solved-dir /path/to/solved` to scan another export directory.
Explicit `--solved-dir` options replace the default directories, so repeat the
option for every directory you want checked.

Problems run sequentially. `--parallel-samples 2` runs two samples within each
problem; change it or pass other normal MiniProver options after `--`. The example
selects OpenAI explicitly. Provider credentials and MiniProver configuration work
as usual.

The sweep displays each run's normal MiniProver progress lines in the terminal
and keeps the same output, including stderr, in `attempt_NNN.sweep_console.log`
beside that attempt's directory. Python workers run unbuffered; the sweep relays available
output on each polling tick (one second by default), including during shutdown.
It displays progress that MiniProver emits; a provider call that emits nothing
can still be quiet until the next MiniProver message.
If a terminal or pipe cannot keep up, live output may lag or be incomplete at
shutdown; the complete output remains in the console log. Console backpressure
does not suspend acceptance-deadline or worker-cleanup checks. After cleanup,
the relay allows up to 0.25 seconds for final output to drain.

Both shell launchers resolve relative paths from the repository root and forward
the current MiniProver options, including provider, model, reasoning, and timeout
settings. Use `./scripts/sweep_putnam_unsolved.sh --help` for sweep controls and
`./scripts/run_mini_unattended.sh --help` for MiniProver controls.

## Acceptance deadlines

Each problem gets one clock, starting before its MiniProver process launches:

| Time from launch | Requirement to continue |
| --- | --- |
| 1,200 seconds | At least one distinct, newly accepted proof |
| 1,800 seconds | At least two distinct, newly accepted proofs |

Accepted proofs are committed Lean-verified helpers or completed subgoal/root
proofs. Samples and recursive children share these milestones. Repeated proofs
of the same canonical proposition, formatting changes, cache/import restoration,
failed checks, and proposed plans do not earn extra milestones. A completed
problem finishes normally.

These are **absolute deadlines**, not rolling inactivity timers. For example,
a first acceptance at 1,190 seconds leaves until 1,800 seconds for the second.
After two timely acceptances, these gates impose no further cutoff; MiniProver's
normal budgets still apply and may end an attempt earlier.
The sweep does not add `run_mini_unattended.sh`'s three time-limit presets. To
bound attempts after they meet both milestones, pass explicit MiniProver budgets
after `--`, for example `--mini-worker-timeout-s 7200`.

The default polling interval is one second. When a deadline is missed, the sweep
signals the CLI and its supervisor, then waits for cleanup before advancing.
Cleanup may take another two minutes. If cleanup cannot be confirmed, the sweep
stops instead of launching another attempt.

An abrupt CLI/supervisor death also stops the sweep. Some signal-related worker
crashes share those exit codes, so the sweep conservatively stops in those cases
even if the supervisor may already have cleaned up.

Override the deadlines before `--`, if needed:

```bash
./scripts/sweep_putnam_unsolved.sh \
  --first-accepted-by-s 1200 --second-accepted-by-s 1800 \
  -- --prover openai --parallel-samples 2
```

## Preview and resume

Preview the complete queue without making provider calls:

```bash
./scripts/sweep_putnam_unsolved.sh \
  --sweep-dir runs/mini_prover/sweeps/putnam-random \
  --dry-run -- --prover openai --parallel-samples 2
```

Start that exact saved queue:

```bash
./scripts/sweep_putnam_unsolved.sh \
  --resume runs/mini_prover/sweeps/putnam-random
```

Use the same resume command after Ctrl-C. Resume preserves the queue, seed,
provider arguments, selection policy, and deadlines. Completed failed/cutoff attempts are skipped;
a cleanly interrupted problem gets a new attempt and fresh clock. A fresh sweep
reconsiders all problems still unsolved. Pass `--seed INTEGER` when creating a
sweep to reproduce its shuffle over the same unsolved set.

Older saved sweeps without a `solved_policy` field retain their original verified
selection policy on resume. Start a fresh sweep to use the new inventory default.

A sweep lock prevents two owners from running the same queue. Resume refuses an
attempt left running or with unconfirmed cleanup after a crash; inspect its
recorded PID and logs before recovering it. It also refuses changed problem
sources. Do not edit the manifest to bypass these checks while work is active.

## Results

The command prints the sweep directory. Its `manifest.json` stores the saved
order, source hashes, commands, statuses, accepted identities and their elapsed
times, cutoff reasons, exit codes, and per-attempt paths. The `console_log` field
records the log path before the worker starts. MiniProver artifacts live in the
attempt directory; the sweep console log lives beside it so checkpoint startup
receives a fresh generation directory. For example:

```text
runs/mini_prover/sweeps/<sweep>/manifest.json
runs/mini_prover/sweeps/<sweep>/attempts/0001_putnam_1978_b2/attempt_001/
runs/mini_prover/sweeps/<sweep>/attempts/0001_putnam_1978_b2/attempt_001.sweep_console.log
```

Older sweeps retain their original `attempt_001/sweep_console.log` files. Their
manifests remain readable; new attempts use the sibling log location.

The Python entry point is equivalent to the wrapper:

```bash
./.venv/bin/python -m ensemble_prover.putnam_sweep --help
```
