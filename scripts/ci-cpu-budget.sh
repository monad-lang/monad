#!/usr/bin/env bash
# Decide how many ways the corpus sweep shards, and put the answer in
# MONAD_SWEEP_JOBS.
#
# It is a script, and CI runs it INSIDE the dev shell, because of a red
# pipeline: a bare `run:` step in these jobs uses the RUNNER HOST's PATH, not
# the dev shell's, and that PATH carries only the nix store entries the runner
# itself needs. It has no `awk` and no `lscpu`. Run 36313431973's `test` job --
# that job is `compiler-checks` now, and it runs this same script -- died 8 s in
# on
#
#   line 4: lscpu: command not found
#   line 7: awk: command not found
#   Process completed with exit code 127
#
# before it had measured anything at all. `nproc` and `uname` DO exist there
# (the same log printed "nproc (affinity-aware): 8" before dying), so the
# workflow step still prints the host reading for contrast -- but everything
# that needs a real tool runs here, in the dev shell, where the sweep itself
# runs.
#
# DECLARING THE TOOLS IS THE OTHER HALF, and both halves are needed. Moving
# the measurement into a script fixed `awk` -- which the dev shell does supply
# -- and left `lscpu`, which it does not: `lscpu` was resolving to
# /run/current-system/sw/bin/lscpu, the AMBIENT system PATH that `nix develop`
# leaves in place rather than replacing, so every CI run after that printed
#
#   /run/github-runner/.../scripts/ci-cpu-budget.sh: line 55: lscpu: command not found
#
# (run 36322856497). It did not fail the step -- the `|| true` held, and the
# step went `completed/success` -- but a green step that prints "command not
# found" is how a real failure gets skimmed past, and `type -p` inside the dev
# shell on the dev box is precisely what made it look fine: it answers a path
# from the system profile, not from the shell, and the runner has no such
# path. So the tools this script calls are now DECLARED in nix/packages.nix (gawk,
# coreutils, gnugrep, util-linux) instead of being ambient luck, and the
# `lscpu` call stays `command -v`-guarded so that dropping util-linux again
# costs a diagnostic line rather than the step. The model name and logical
# count come from /proc/cpuinfo, which needs no tool at all; `lscpu` adds its
# own view (the scaling-MHz line is the part /proc/cpuinfo does not give).
#
# The two the DECISION needs -- `nproc` and `awk` -- are checked for rather
# than assumed, because a budget computed from a missing tool is worse than a
# loud failure.
#
# The numbers, and why each is printed rather than asserted:
#
#   * there was never a disagreement to settle -- there were TWO MACHINES.
#     This repository's ci.yml asserted the sweep's default was "= 7 here",
#     monad-nixos-modules' runner module comments 8 vCPU as "matches the CI
#     host's cores", and run 36301331844 shipped 3 shards. All three were
#     right, about different hosts: `runs-on: [self-hosted, linux]` reaches
#     both runners, and "Set up job" names the one that took the job.
#     nixos-server (4 cores, 15.6 GB) gave 3 shards in 36301331844;
#     anders-desktop (8 cores, 31.3 GB) gave 7 in 36322856497. Both readings
#     below are therefore per-MACHINE, and no literal belongs in the workflow.
#   * `nproc` respects this process's CPU affinity and the cgroup CPU quota
#     caps the CPU time it may actually burn, so the smaller of the two is the
#     budget. `cpu.max` is absent on both runners (printed as such), which
#     makes the quota the affinity there -- but the reading is printed either
#     way, so a runner that does constrain it says so instead of silently
#     changing the answer.
#   * the budget IS the shard count -- one shard per core. That reverses the
#     `nproc - 1` this script and the sweep's default used to carry: a shard
#     count below the core count can only lengthen the phase's wall (the
#     LARGEST shard) or leave it unchanged, never shorten it, so the reserved
#     core bought nothing and a round-1 inheritance cost whatever imbalance it
#     absorbed. No size for that cost is claimed here -- round 2's estimate
#     (a 3797 s sum from run 36323615273's `947s 1425s 1425s`) and run
#     36336502690's `1220s` seven times were both read off per-shard
#     instrumentation that was reporting a running maximum, not each shard's
#     own duration (see `run_shards` in scripts/check-monad-tests.sh), so the
#     first correct per-shard numbers are the next run's, not these.
#   * what a shard count ABOVE the core count costs was measured next
#     (2026-10-02, `taskset -c 0-3`, warm compiler, cold store between runs,
#     the same 231-file corpus): the phase wall -- the LARGEST shard -- was
#     1233 s at 4 shards, 1283 s at 8 and 1160 s at 12, a 124 s band, while the
#     summed per-shard wall grew 3849 -> 6990 -> 9016 s as more processes
#     shared four cores. Oversubscribing bought nothing and 8 was the slowest
#     of the three, which is why this script stays at one shard per core
#     instead of splitting finer to chase the ~271 s between the 4-shard wall
#     and the 962 s the 3849 s of work would take on four cores: that residue
#     is the machine and its co-tenants, not the split. The sweep's own
#     per-process warm-up is ~13 s (a fresh `monad test` on a file with no
#     tests, cold store), far too small to be why the count does not scale.
#   * the cap of 8 is a guard on shard COUNT, not on memory. The memory
#     reasoning it used to carry ("this corpus has OOM'd a box before") does
#     not survive contact with the corpus as it now is: `monad test
#     lang/src/scope.mo`, the heaviest file in it, peaks at 172 MB of summed
#     tree RSS (measured 2026-09-27), so four shards are well under a gigabyte
#     on the 15.6 GB runner. It stays because no runner in this fleet has more
#     than 8 cores, and a workstation that is also a runner should not be
#     asked for more than that -- the measurement above says a count past the
#     core count is worth avoiding, so on a machine with more cores than this
#     fleet has, raising the cap means re-measuring rather than assuming.
#   * the reading that chose the shard count comes from `nproc` INSIDE the dev
#     shell, so this script -- which runs there -- prints its own `nproc`, and
#     the step prints the host's beside it. Both are in the log, so a shard
#     count that surprises anyone can be traced to the machine that produced
#     it rather than to memory.
#
# It is runnable by hand, which is how the dependencies above were checked:
#
#   DEVENV_SKIP_TASKS=1 nix develop --no-pure-eval --accept-flake-config \
#     -c scripts/ci-cpu-budget.sh
#
# With GITHUB_ENV unset it prints the line instead of exporting it, so a local
# run says what it WOULD have set rather than writing to a file that is not
# there.
set -euo pipefail

# The two the decision needs. Checked, not assumed: `nproc` with no core count
# and `awk` with no parser would silently produce a wrong budget, and a wrong
# budget is a shard count nobody can explain from the log.
for tool in nproc awk; do
  if ! command -v "$tool" > /dev/null; then
    echo "ci-cpu-budget: $tool is required and is not on this PATH" >&2
    exit 2
  fi
done

echo "runner: $(uname -n)"
echo "nproc (this environment's affinity): $(nproc)"
echo "nproc --all: $(nproc --all)"
model="$(awk -F': ' '/^model name/ { print $2; exit }' /proc/cpuinfo || true)"
logical="$(awk '/^processor/ { n++ } END { print n + 0 }' /proc/cpuinfo || true)"
echo "cpu: ${model:-unknown} x ${logical:-?} logical (from /proc/cpuinfo, which needs no tool)"
# Declared in nix/packages.nix, so this resolves on the runner as well; the guard is
# what keeps a future removal to a missing line rather than a failed step.
if command -v lscpu > /dev/null; then
  lscpu | grep -E '^CPU\(s\)|^Model name' || true
fi
echo "cpu.max: $(cat /sys/fs/cgroup/cpu.max 2> /dev/null || echo absent)"
echo "memory.max: $(cat /sys/fs/cgroup/memory.max 2> /dev/null || echo absent)"
awk '/^MemTotal/ { print "MemTotal: " $2 " kB" }' /proc/meminfo

affinity="$(nproc)"
quota="$(awk '{ if ($1 != "max" && $2 > 0) { q = int($1 / $2); if (q > 0) print q } }' \
  /sys/fs/cgroup/cpu.max 2> /dev/null || true)"
budget="$affinity"
if [ -n "$quota" ] && [ "$quota" -lt "$budget" ]; then
  budget="$quota"
fi
# One shard per core, with nothing held back -- see the shard-walls bullet in
# the header for why the old `- 1` was costing a quarter of the sweep.
jobs="$budget"
if [ "$jobs" -lt 1 ]; then jobs=1; fi
if [ "$jobs" -gt 8 ]; then jobs=8; fi
echo "budget: affinity=$affinity quota=${quota:-unlimited} -> $jobs sweep shard(s)"

if [ -n "${GITHUB_ENV:-}" ]; then
  echo "MONAD_SWEEP_JOBS=$jobs" >> "$GITHUB_ENV"
else
  echo "MONAD_SWEEP_JOBS=$jobs (GITHUB_ENV is unset: printed, not exported)"
fi
