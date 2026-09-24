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
# modes below now cmp their second turn. The `ulimit -s` is load-bearing for
# exactly the turn this adds -- the second turn is the binary interpreting
# ITSELF, which is where the ladder's own rung-2 first hit the default 8MB
# stack (`|| true` keeps a runner whose HARD limit is lower at its own
# ceiling rather than failing the job).
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

ulimit -s 131072 || true

out="${TMPDIR:-/tmp}/monad-bootstrap-ci"
rm -rf "$out"; mkdir -p "$out"
# No timeout, by design: the interpreted self-compile measured ~320s
# (2026-09-09) but stretches 2-4x when the runner's other jobs and local
# sessions share this machine, and `cargo run`'s own build phase is ~10 min
# cold (fat-LTO profile; CI's ephemeral job containers never have a warm
# target/). A fixed `timeout` here was killing healthy runs; the job-level
# `timeout-minutes` is the hang guard. Progress is visible instead: --verbose
# streams a per-module and per-stage trace (std/src/log.mo), so a genuinely
# wedged run shows exactly which stage stalled.
# --release: debug info is on by default; DWARF emission costs ~30s on this
# workload and the binary this job tests does not need it.
cargo run --release -- run cli/src/main.mo compile cli/src/main.mo -o "$out/monad" --verbose --release
test -x "$out/monad"
"$out/monad" check cli/src/main.mo
# ... and the FIXPOINT, which is the property that would regress silently: the
# binary just built compiles the same source itself, and the `.ll` it emits
# (written beside its own `-o` output) must be byte-identical to the host's.
# Rung 1 == rung 2, asserted rather than remembered. A binary that builds and
# checks but emits different IR for its own source is a miscompile the
# front-end tests cannot see.
"$out/monad" compile cli/src/main.mo -o "$out/monad2" --release
test -x "$out/monad2"
cmp "$out/monad.ll" "$out/monad2.ll"

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
dbg="${TMPDIR:-/tmp}/monad-bootstrap-ci-debug"
rm -rf "$dbg"; mkdir -p "$dbg"
cargo run --release -- run cli/src/main.mo compile cli/src/main.mo -o "$dbg/monad" --verbose
test -x "$dbg/monad"
"$dbg/monad" check cli/src/main.mo
# Same fixpoint in the default (DWARF-emitting) mode -- see the `--release`
# block above for why both turns are asserted.
"$dbg/monad" compile cli/src/main.mo -o "$dbg/monad2"
test -x "$dbg/monad2"
cmp "$dbg/monad.ll" "$dbg/monad2.ll"
