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
Previously failed attempts remain eligible. The existing solved-export scanner
excludes problems with verified, matching Lean exports in `runs/mini_prover/solved`
or `runs/solved`, and checks again before each launch.
The queue size depends on your local corpus and solved exports.
Add `--solved-dir /path/to/solved` to scan another export directory.
Explicit `--solved-dir` options replace the default directories, so repeat the
option for every directory you want checked.

Problems run sequentially. `--parallel-samples 2` runs two samples within each
problem; change it or pass other normal MiniProver options after `--`. The example
selects OpenAI explicitly. Provider credentials and MiniProver configuration work
as usual.

## Acceptance deadlines

Each problem gets one clock, starting before its MiniProver process launches:

| Time from launch | Requirement to continue |
| --- | --- |
| 600 seconds | At least one distinct, newly accepted proof |
| 1,800 seconds | At least two distinct, newly accepted proofs |

Accepted proofs are committed Lean-verified helpers or completed subgoal/root
proofs. Samples and recursive children share these milestones. Repeated proofs
of the same canonical proposition, formatting changes, cache/import restoration,
failed checks, and proposed plans do not earn extra milestones. A completed
problem finishes normally.

These are **absolute deadlines**, not rolling inactivity timers. For example,
a first acceptance at 590 seconds leaves until 1,800 seconds for the second.
After two timely acceptances, these gates impose no further cutoff; MiniProver's
normal budgets still apply and may end an attempt earlier.

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
  --first-accepted-by-s 600 --second-accepted-by-s 1800 \
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
provider arguments, and deadlines. Completed failed/cutoff attempts are skipped;
a cleanly interrupted problem gets a new attempt and fresh clock. A fresh sweep
reconsiders all problems still unsolved. Pass `--seed INTEGER` when creating a
sweep to reproduce its shuffle over the same unsolved set.

A sweep lock prevents two owners from running the same queue. Resume refuses an
attempt left running or with unconfirmed cleanup after a crash; inspect its
recorded PID and logs before recovering it. It also refuses changed problem
sources. Do not edit the manifest to bypass these checks while work is active.

## Results

The command prints the sweep directory. Its `manifest.json` stores the saved
order, source hashes, commands, statuses, accepted identities and their elapsed
times, cutoff reasons, exit codes, and per-attempt paths. Each attempt contains
the usual MiniProver artifacts plus `sweep_console.log`. For example:

```text
runs/mini_prover/sweeps/<sweep>/manifest.json
runs/mini_prover/sweeps/<sweep>/attempts/0001_putnam_1978_b2/attempt_001/
```

The Python entry point is equivalent to the wrapper:

```bash
./.venv/bin/python -m ensemble_prover.putnam_sweep --help
```
