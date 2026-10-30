#!/usr/bin/env bash
# The bootstrap ladder AND the self-hosted sweep, in one job and at once.
#
# CI's `compiler-checks` job runs this instead of two jobs. Two things are
# bought by that, and only one of them is the runner queue:
#
#   * `test` could not start until a runner was free, and `bootstrap` -- the
#     SHORTER job -- kept taking it first. Run 36914860312: `changes` freed a
#     runner at 19:31:12, `bootstrap` took it at 19:31:14, and `test` sat in
#     the queue until 19:41:00, ten minutes of a 49-minute job spent waiting
#     for a machine that was running the other half of the same work.
#   * The compiler the sweep grades IS the ladder's release rung-1
#     (`<target-dir>/bootstrap-ci/monad`), so the sweep can start as soon as
#     that binary exists rather than after the ladder has also run
#     `check cli/src/main.mo` and its fixpoint turn -- and, in the old split,
#     rather than after the flake had built a SECOND rung-1 of its own. One
#     interpretation instead of two, overlapped instead of serial.
#
# WHY THE WAIT IS ON A MARKER FILE, NOT ON THE BINARY. `scripts/build-self-hosted.sh`
# builds with the compiler's own `build cli/src/main.mo -o "$out/monad"`
# (build-self-hosted.sh:118), which creates the output as it links it -- so
# `[ -x "$out/monad" ]` can be true of a half-written ELF, and a sweep started
# on that grades a truncated compiler. `scripts/bootstrap-compile.sh` writes
# `$dir/rung1.done` the moment its rung-1 build has RETURNED, in both branches
# (the from-source build and the store re-use), so this waits for a signal that
# cannot be early. Nothing else reads it, and `ladder()`'s own `rm -rf "$dir"`
# at the top of every run means a marker can never survive into another one --
# but it is removed here too, before the ladder starts, because a leftover from
# a local run is exactly the kind of stale evidence that would make this wait
# return instantly and grade a week-old compiler.
#
# The sweep's output goes straight to stdout and the ladder's keeps its own
# `[release]` / `[debug]` prefixes (bootstrap-compile.sh adds them, for the
# reason it states: two unprefixed streams on one terminal are no longer
# evidence of which half stalled). So in this job's log an UNPREFIXED line is
# the sweep and a prefixed one is a ladder, which is why nothing here adds a
# third prefix.
#
# The sweep gets its OWN target dir, and not for speed -- nothing can reuse
# what it writes. It is the one writer that can collide with the ladder:
# `Build.check_key` is `sha256(file_digest ++ closure ++ compiler)` with no
# profile in it (build/src/check.mo), the ladder's `check cli/src/main.mo` runs
# the rung-1, and `cli/src/main.mo` is also in the sweep's corpus -- one file,
# one closure, one compiler identity, therefore one entry, written by two
# processes at once through a non-atomic `IO.write_file`
# (`Build.check_entry_write`, build/src/check.mo:421). The payloads agree
# (same inputs, same compiler), so what that buys is a reader catching a
# half-written file; the collision is real and not worth reasoning about
# further when the fix is one line.
#
# The LADDER keeps the default target dir, because its entries are worth
# keeping: its rung-1 build is the HOST interpreting the tree, so an unchanged
# tree rebuilds from the store in seconds instead of in 22 minutes -- which is
# most of what `MONAD_RUNG1_STORE` was reaching for, and this costs nothing.
# The sweep's entries are keyed on the rung-1's own digest, which moves
# whenever the tree does, so nothing outside this job could have used them.
#
# `MONAD_SWEEP_JOBS` is left to scripts/ci-cpu-budget.sh, the way the `test`
# job left it: the sweep and the ladder's tail overlap on one core for a couple
# of minutes out of twenty, and a shard is not worth giving up for that.
#
# Runnable by hand, which is how it was checked rather than assumed:
#
#   MONAD_HOST_BIN=rust/target/release/monad-rs scripts/ci-compiler-checks.sh
#
# with the same warning every other sweep carries: do not edit the tree while
# it runs.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

# shellcheck disable=SC2034  # read by the sourced helper, not here
MONAD_REPO_ROOT="$root"
# shellcheck source=scripts/lib/bootstrap-dir.sh
# shellcheck disable=SC1091  # the hook runs bare `shellcheck`; the line above names the path for -x
. "$root/scripts/lib/bootstrap-dir.sh"

# The `-debug` sibling of this name is bootstrap-compile.sh's second ladder;
# this one is the sweep's target dir, under the same `target-monad/` and moved
# by the same `MONAD_BOOTSTRAP_DIR`.
sweep_target="${MONAD_BOOTSTRAP_DIR}-sweep"

marker="$MONAD_BOOTSTRAP_DIR/rung1.done"
rm -f "$marker"

# 3600s is a hang guard, not a deadline for the build: the interpreted
# self-compile is ~20-23 min on both runners and stretches under load from the
# runner's own jobs. The job-level `timeout-minutes` is the outer guard; this
# one exists so a wedge that never produces a binary reports WHICH wait it was
# in rather than dying as a bare job timeout.
deadline=$((SECONDS + 3600))

echo "ci-compiler-checks: starting the ladder; the sweep follows $marker"
scripts/bootstrap-compile.sh &
ladder=$!

while [ ! -f "$marker" ]; do
  # `kill -0`, never `pgrep -f`: a pattern like this matches the watcher's own
  # command line, so the watcher sees itself and never notices the process it
  # was actually waiting for.
  if ! kill -0 "$ladder" 2>/dev/null; then
    ladder_rc=0; wait "$ladder" || ladder_rc=$?
    echo "ci-compiler-checks: the ladder exited $ladder_rc before writing $marker -- run scripts/bootstrap-compile.sh on its own to see why; the sweep was NOT run" >&2
    exit 1
  fi
  if [ "$SECONDS" -ge "$deadline" ]; then
    echo "ci-compiler-checks: no rung 1 after $((SECONDS))s -- killing the ladder; the sweep was NOT run" >&2
    kill "$ladder" 2>/dev/null || true
    exit 1
  fi
  sleep 5
done

echo "ci-compiler-checks: rung 1 is in place after $((SECONDS))s; sweeping with $MONAD_BOOTSTRAP_BIN while the ladder finishes"
sweep_rc=0
MONAD_BIN="$MONAD_BOOTSTRAP_BIN" MONAD_TARGET_DIR="$sweep_target" \
  scripts/check-monad-tests.sh || sweep_rc=$?

ladder_rc=0
wait "$ladder" || ladder_rc=$?
if [ "$sweep_rc" -ne 0 ] || [ "$ladder_rc" -ne 0 ]; then
  echo "ci-compiler-checks: the sweep exited ${sweep_rc}, the ladder ${ladder_rc}" >&2
  exit 1
fi
echo "ci-compiler-checks: the sweep and the ladder both passed"
