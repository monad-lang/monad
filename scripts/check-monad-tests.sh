#!/usr/bin/env bash
# The full .mo test sweep, run by `tasks."monad:test"` in devenv.nix
# (which CI's `test` job invokes). prek does not invoke a shell, so a
# hook entry cannot chain commands -- hence this wrapper script.
#
# Runs the SELF-HOSTED test runner (`monad test`, implemented in
# lang/src/codegen/test_driver.mo + cli/src/main.mo), not the Rust
# evaluator: that runner is what the project ships, and until this
# switched, nothing in CI exercised it over the whole corpus. It
# compiles a driver binary per test file and runs it, so a test failure
# here is a failure of real compiled code.
#
# The binary has to be built in this job: CI's `test` and `bootstrap`
# jobs run in separate ephemeral containers, so neither can borrow the
# other's artifacts. The staleness check mirrors
# `tasks."monad:debug-oracle"` -- reuse an existing binary, but rebuild
# when any source compiled INTO it is newer, since a stale compiler
# reports failures that are really its own age. All four motes, not
# just lang/: cli/ holds the compile target, llvm/ and runtime/ the
# backend.
#
# Known gap: `std/src/concurrent/fiber_test.mo` and `combine_test.mo`
# are SKIPped, not run -- their tests reach concurrency natives that the
# native backend does not wire, so the driver cannot be compiled at all.
# They are deferred until a self-hosted async runtime exists; the runner
# reports them as skips with that reason rather than failing.
set -euo pipefail
out="${TMPDIR:-/tmp}/monad-bootstrap-ci"
if [ ! -x "$out/monad" ] || [ -n "$(find lang cli llvm runtime -name '*.mo' -newer "$out/monad" -print -quit)" ]; then
  mkdir -p "$out"
  cargo run --release -- run cli/src/main.mo compile cli/src/main.mo -o "$out/monad" --release
fi
test -x "$out/monad"
"$out/monad" test init std examples lang cli llvm runtime motes slow_tests
