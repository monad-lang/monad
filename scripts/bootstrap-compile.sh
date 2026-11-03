#!/usr/bin/env bash
# The self-hosted compiler compiles ITSELF, and then the binary that falls
# out has to do the job it was built for.
#
# The second step is the one with teeth. `compile` succeeding only says
# llc and clang were happy with the emitted IR; it says nothing about
# whether the binary works, and a compiler that builds but miscompiles
# is worse than one that fails to build. Running `check cli/src/main.mo`
# through it costs ~12s and exercises the whole front end -- parser,
# scope, elaboration, typechecker -- on the largest input in the tree.
#
# What this deliberately does NOT check is the fixpoint: that the `.ll`
# this binary produces from the same source is byte-identical to the one
# the host produced (it is, and all three stages agree bit-for-bit), and
# that the same holds one more turn out. That is the stronger property
# and the one that would regress silently, but it costs another full
# self-compile per turn. It got cheap enough (2026-09-19): the self-hosted
# compile is ~40s interpreted against ~320s when this was written, so both
# modes below now cmp their second turn. The stack raise is load-bearing for
# exactly the turn this adds -- the second turn is the binary interpreting
# ITSELF, which is where the ladder's own rung-2 first hit the default 8MB
# stack -- and it lives in scripts/lib/raise-stack.sh now, shared with the
# other two scripts that need it.
#
# This is called by .github/workflows/ci.yml and .tangled/workflows/bootstrap.yml
# directly, inside one `nix develop -c`, rather than through
# `devenv tasks run monad:bootstrap-compile` (which is the local equivalent):
# devenv-tasks captures a task's stdout and shows it only when the task FAILS,
# which would swallow the --verbose per-module and per-stage trace below -- the
# evidence that says where a wedged or miscompiling run actually stalled. The
# task in devenv.nix runs this same script in this same dev shell, just quieter
# on success.
#
# Commands run bare in a `run:` get the RUNNER HOST's PATH, not the dev shell's,
# so a tool is only a declared dependency when it comes through `nix develop`.
# That is why the whole pipeline lives here rather than in the workflow YAML.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

# One definition, shared with scripts/build-self-hosted.sh and
# scripts/self-compile-turn.sh -- see scripts/lib/raise-stack.sh.
# shellcheck source=scripts/lib/raise-stack.sh
# shellcheck disable=SC1091  # the hook runs bare `shellcheck`; the line above names the path for -x
. "$root/scripts/lib/raise-stack.sh"

# The scratch directory, private to this checkout. One definition, shared with
# check-monad-tests.sh, debug-oracle.sh and tools/debug_transparency_oracle.sh
# -- see scripts/lib/bootstrap-dir.sh, including why TMPDIR is no longer
# consulted for this path.
# shellcheck disable=SC2034  # read by the sourced helper, not here
MONAD_REPO_ROOT="$root"
# shellcheck source=scripts/lib/bootstrap-dir.sh
# shellcheck disable=SC1091  # the hook runs bare `shellcheck`; the line above names the path for -x
. "$root/scripts/lib/bootstrap-dir.sh"
out="$MONAD_BOOTSTRAP_DIR"
# No timeout, by design: the interpreted self-compile measured ~320s
# (2026-09-09) but stretches 2-4x when the runner's other jobs and local
# sessions share this machine. A fixed `timeout` here was killing healthy
# runs; the job-level `timeout-minutes` is the hang guard. Progress is
# visible instead: --verbose streams a per-module and per-stage trace
# (std/src/log.mo), so a genuinely wedged run shows exactly which stage
# stalled.
#
# The interpreter the two builds below run is the job's `MONAD_HOST_BIN`,
# which CI's `compiler-checks` job sets to the flake's packaged host
# (`nix build .#monadHost`); unset, scripts/build-self-hosted.sh falls back to
# `cargo run --release --`, whose cold fat-LTO build was ~10 minutes here
# (actions/checkout runs git clean -ffdx at the start of every job, wiping
# both target directories, .devenv/ and the config, so it was cold every time).
#
# RUNG 1 ITSELF IS NOW ALSO AVAILABLE AS A PACKAGE, and the release ladder
# takes it when this machine's store already holds it -- see the block above
# `ladder()`. That reverses what stood here, which was that a store compiler
# "has no `.ll` beside it (nix/monad.nix does not install one)": `nix/monad.nix`
# now splits rung 1 into `packages.monadRung1`, and that output DOES install the
# `.ll` the interpreter wrote, precisely so this comparison can be made against
# a re-used rung 1 rather than only a re-built one. CI's `compiler-checks` job
# has no such comparison to make, so it sweeps the release rung-1 this script
# builds -- see its step in scripts/ci-compiler-checks.sh.
#
# --release: debug info is on by default; DWARF emission costs ~30s on this
# workload and the binary this job tests does not need it. So the release
# ladder is the fast one and the default-mode ladder is the one that gates
# DWARF emission -- and, because both are asserted, the mode flag is threaded
# through every command below rather than set on one of them.
#
# One ladder, both modes: build rung 1, check the largest input in the tree
# through it, then assert the FIXPOINT -- the binary just built compiles the
# same source itself, and the `.ll` it emits (written beside its own `-o`
# output) must be byte-identical to the host's. Rung 1 == rung 2, asserted
# rather than remembered. A binary that builds and checks but emits different
# IR for its own source is a miscompile the front-end tests cannot see.
#
# The turn itself is scripts/self-compile-turn.sh -- the same command, with
# the same absolute `-o` and the same post-condition, that the flake's
# `checks.bootstrap` runs against the packaged compiler. One definition, so
# the two ladders cannot drift.
#
# The only difference between the two callers is `--release` (see each one's
# note below), and it is threaded through to BOTH commands: `--release` on the
# compile is what decides whether DWARF is emitted, and `--release` on the turn
# is what keeps the emitted IR comparable to it. `rm -rf` forces a
# from-scratch build rather than trusting a stale binary; the staleness check
# and the build command live in scripts/build-self-hosted.sh.
#
# A3 -- rung 1 is a package, and the release ladder takes it from the store
# when the store already holds it.
#
# `nix/monad.nix`'s `packages.monadRung1` IS this ladder's rung 1: the host
# interpreting the compiler's own sources, with the `.ll` it emitted installed
# beside the binary. The from-source build below computes exactly that, so when
# the store already has it the build adds nothing but the wait -- and the `.ll`
# it would have written is the very file `cmp` below is a comparison against.
#
# THREE THINGS BOUND IT, all measured rather than assumed:
#
#   * It is RELEASE-ONLY. The two ladder modes' IR differs decisively -- measured
#     on this tree: the release `.ll` is 5510916 bytes and the DWARF mode's
#     8947320, differing from byte 229476 -- so one stored rung 1 cannot serve
#     both, and the debug ladder keeps its from-source build. The step's wall is
#     the SLOWER ladder, and the ladder that sets it is the one that cannot
#     consume this. The saving is therefore runner CPU on the release ladder, NOT
#     the step's wall clock; said plainly here so a CI log is not read as a win it
#     cannot make.
#   * A hit is OPPORTUNISTIC. The fleet's two runners share no nix store, and
#     `ci.yml` already records that. It hits on a re-run, on a commit that
#     leaves the compiler's sources alone, or on a machine that has already
#     built the package -- and since the release family moved to the
#     nightly-hosted rung (nix/nightly.nix), nothing in a PR pipeline
#     realizes `monadRung1` any more: `.#monad` depends on
#     `monadNightlyRung1` instead, and `compiler-checks` builds its rung-1
#     from source in its own scratch directory and no longer goes through
#     the flake at all. What puts it in a runner's store is the NIGHTLY's
#     cache push (nightly.yml names it beside the rungs it builds), so a
#     machine that has only swept has NOT got this.
#   * `nix-store --check-validity` asks "is it already realized", which is the
#     question. `nix build` would answer it by BUILDING, which is the ~320 s of
#     interpretation this exists to avoid; `nix eval` of the output path carries
#     no such risk, since it evaluates the derivation without realizing it.
#
# The path is content-addressed on the compiler's SOURCES and not on the commit
# (that being the split `nix/monad.nix` performs), so it cannot be a stale hit:
# a dirty or moved source tree evaluates to a different path and the from-source
# build runs. Nothing here asserts anything about the binary's revision -- the
# ladder never checked one, and `cmp` below is what it checks.
rung1_store="${MONAD_RUNG1_STORE:-}"
if [ -z "$rung1_store" ]; then
  rung1_store="$(nix eval --raw .#monadRung1.outPath 2>/dev/null || true)"
fi

# Usable only if it is realized AND carries the `.ll`. The second test is not
# redundant: it is the one that fails first and most legibly if a later edit
# stops installing the IR, which is the single thing this lever depends on.
rung1_in_store() {
  [ -n "$rung1_store" ] || return 1
  [ -f "$rung1_store/share/monad/monad.ll" ] || return 1
  nix-store --check-validity "$rung1_store" 2>/dev/null
}

ladder() {
  local dir="$1" store_rung1="$2"; shift 2
  rm -rf "$dir"; mkdir -p "$dir"
  # The WRAPPER (`bin/monad`), not `share/monad/monad`: the compiler shells out
  # to bare `llc` and `clang`, and the wrapper is what puts them on PATH and
  # supplies the gc header and library. Handing it the raw binary would make
  # this depend on the dev shell happening to provide both.
  #
  # A SYMLINK, and the LINK's own mtime is load-bearing. `debug-oracle.sh` --
  # the step immediately after this one in the same CI job -- runs
  # `build-self-hosted.sh` on this same directory, whose staleness scan is
  # `find <the compiler's trees> ... -newer "$out/monad"` (that script's header
  # has the live list; it has grown twice, so it is not repeated here). `ln -sfn`
  # stamps the link with NOW, so the scan finds nothing newer and the oracle
  # reuses this compiler; the store file's own mtime is 1970-01-01 (measured),
  # so a copy that PRESERVED it (`cp -p`, `cp -a`) would read as stale and send
  # the oracle into a from-source rebuild writing over a read-only store path.
  # Measured rather than assumed, both directions: the same scan against the
  # store path directly reports `init/mote.toml` (stale), against this symlink
  # it reports nothing (fresh).
  if [ "$store_rung1" = 1 ] && rung1_in_store; then
    echo "rung 1: re-using the store build at $rung1_store -- the interpretation is skipped"
    ln -sfn "$rung1_store/bin/monad" "$dir/monad"
    install -m644 "$rung1_store/share/monad/monad.ll" "$dir/monad.ll"
  else
    scripts/build-self-hosted.sh "$dir" --verbose "$@"
  fi
  # RUNG 1 IS FINISHED, and this is how the merged CI job learns it. The sweep
  # grades this binary, and in `compiler-checks` it runs CONCURRENTLY with the
  # rest of this function (the check and the fixpoint turn below), so it has to
  # know when the build has returned. It waits on this marker rather than on
  # `[ -x "$dir/monad" ]` because `build-self-hosted.sh` builds with the
  # compiler's own `build -o "$dir/monad"`, which creates that file as it links
  # it -- an executable that is still half-written would start a sweep grading
  # a truncated compiler. Reached on BOTH branches above, so a store re-use
  # signals too. Nothing else reads it (`rm -rf "$dir"` at the top of this
  # function clears it, so it cannot survive into another run of the ladder),
  # and it is deliberately touched before `check`: a rung-1 that fails to check
  # the corpus is still the rung-1 the sweep is entitled to grade, and the
  # ladder's own verdict stays the ladder's.
  : > "$dir/rung1.done"
  "$dir/monad" check cli/src/main.mo
  scripts/self-compile-turn.sh "$dir/monad" "$dir" monad2 "$@"
  cmp "$dir/monad.ll" "$dir/monad2.ll"
}

# The two ladders are INDEPENDENT -- separate output directories, separate
# builds, nothing shared but the read-only sources -- so they run at once
# rather than one after the other. Measured: 38m53s together in the job that
# was then `bootstrap` (run 36243944155), and 25m25s in run 36914860312, where
# the step is the whole of `compiler-checks`' ladder half.
# Each ladder is single-threaded -- one `llc`, one `clang` at a time -- so
# overlapping them uses a second core of the runner's eight rather than
# contending for the first, and the step's wall clock becomes the slower
# ladder instead of their sum.
#
# Memory is the thing this trades away, so it is stated with its measurement
# rather than assumed: each rung-1 build is the Rust host interpreting
# cli/src/main.mo, sampled at 1.34 GB RSS on this workload, so both at once is
# ~2.7 GB plus the dev shell -- not the 29.7 GB shape that OOM'd a machine
# once (that was a compiled binary with no release calls; see
# runtime/src/runtime.c).
#
# Each ladder's `--verbose` trace is prefixed rather than interleaved: the
# trace is the evidence that says where a wedged or miscompiling run stalled,
# and two unprefixed streams on one terminal are no longer evidence of which
# ladder stalled -- which is also why they stream rather than being captured
# to a file and printed only on failure.
#
# `exit "${PIPESTATUS[0]}"` is explicit because `set -e` does NOT reliably
# propagate a failure out of a pipeline's left-hand element: without it a dead
# ladder would exit its own subshell 0 and this script would wait out the
# other one and then report success.
( ladder "$out" 1 --release 2>&1 | sed -u 's/^/[release] /'; exit "${PIPESTATUS[0]}" ) &
release_pid=$!
# And again WITHOUT --release, which is the DEFAULT invocation and was broken
# for an unknown length of time precisely because nothing ran it: `monad
# compile cli/src/main.mo` died at `no instance found for `Append.append``,
# and the only signal was a self-compile nobody waited for (it took 7h48m
# before the located-parse fix).
#
# Both modes share one term tree -- every term carries its source position on
# every path (`parse_all_decls`, lang/module.mo) -- so this run differs from
# the one above only in whether DWARF is EMITTED. That is exactly why it is
# worth running: it is the only gate for the carrier-inference shape probes in
# lang/scope.mo, which no small-file test can reach (see
# examples/located_terms.mo's own header for why, verified rather than
# assumed).
dbg="$MONAD_BOOTSTRAP_DIR-debug"
( ladder "$dbg" 0 2>&1 | sed -u 's/^/[debug]   /'; exit "${PIPESTATUS[0]}" ) &
debug_pid=$!

release_rc=0; wait "$release_pid" || release_rc=$?
debug_rc=0;   wait "$debug_pid"   || debug_rc=$?
if [ "$release_rc" -ne 0 ] || [ "$debug_rc" -ne 0 ]; then
  echo "bootstrap-compile.sh: the release ladder exited ${release_rc}, the debug ladder ${debug_rc}" >&2
  exit 1
fi
