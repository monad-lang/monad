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

# Files the self-hosted runner cannot build a working driver for today,
# each for a separate PRE-EXISTING backend bug -- none of them a problem
# with the test file or with the runner:
#
#   lang/src/parser/position.mo
#   cli/src/tests/cli_derive_self_hosted_tests.mo
#       `llc` rejects the emitted IR ("instruction forward referenced
#       with type 'i64'"): an `icmp` result reaches a `phi i64` from a
#       block emitted after its own use. The bad IR is in a user test's
#       own body -- a `match` arm that reads a struct field -- not in
#       anything the driver generates.
#
#   cli/src/tests/main_tests.mo
#   std/src/list_tests3a.mo
#   std/src/list_tests3b.mo
#   std/src/array.mo
#   examples/iteration_advanced.mo
#       The driver dies by signal. In the emitted `BEq_List_A_beq` the
#       recursive tail comparison applies the ELEMENT dictionary to two
#       lists, dereferencing list cells as scalars.
#
#   lang/src/toml.mo
#       The driver allocates without bound -- OOM-killed at ~30 GB RSS,
#       and no progress in 10 minutes under a 4 GB cap. Its 34 tests pass
#       in milliseconds on the host. This is the no-free-runtime memory
#       pathology (plans/bootstrapping/rung3-oom-no-free-runtime.md),
#       reached by whichever toml test allocates hardest. EXCLUDED FOR
#       THE RUNNER'S SAKE, not just for speed: 30 GB is enough to disturb
#       everything else on a CI machine.
#
# They are NOT dropped from CI: the Rust runner executes them below, so a
# real regression in any of them still fails this script. Delete the
# exclusion (and the second invocation) once the two codegen bugs are
# fixed -- see plans/implementations/2026-09-16-self-hosted-test-runner-parity.md.
out="${TMPDIR:-/tmp}/monad-bootstrap-ci"
if [ ! -x "$out/monad" ] || [ -n "$(find lang cli llvm runtime -name '*.mo' -newer "$out/monad" -print -quit)" ]; then
  mkdir -p "$out"
  cargo run --release -- run cli/src/main.mo compile cli/src/main.mo -o "$out/monad" --release
fi
test -x "$out/monad"

# The self-hosted sweep: everything except the three files above. They sit
# in directories with many healthy files, so the excluded files are named
# individually rather than by pruning their parent directory.
self_hosted_targets=()
while IFS= read -r f; do
  case "$f" in
    lang/src/parser/position.mo) continue ;;
    cli/src/tests/cli_derive_self_hosted_tests.mo) continue ;;
    cli/src/tests/main_tests.mo) continue ;;
    std/src/list_tests3a.mo) continue ;;
    std/src/list_tests3b.mo) continue ;;
    std/src/array.mo) continue ;;
    examples/iteration_advanced.mo) continue ;;
    lang/src/toml.mo) continue ;;
    lang/src/parser.mo) continue ;;
    std/src/list.mo) continue ;;
    lang/src/core_eval.mo) continue ;;
    lang/src/typecheck/meta_eval.mo) continue ;;
    lang/src/tests/core_eval_lang_tests.mo) continue ;;
  esac
  self_hosted_targets+=("$f")
done < <(find init std examples lang cli llvm runtime motes slow_tests -name '*.mo' | sort)

"$out/monad" test "${self_hosted_targets[@]}"

# And every excluded file through the Rust runner, so each stays covered:
# a real regression in any of them still fails this script.
cargo run --release -- test \
  lang/src/parser/position.mo \
  cli/src/tests/cli_derive_self_hosted_tests.mo \
  cli/src/tests/main_tests.mo \
  std/src/list_tests3a.mo \
  std/src/list_tests3b.mo \
  std/src/array.mo \
  examples/iteration_advanced.mo \
  lang/src/toml.mo \
  lang/src/parser.mo \
  std/src/list.mo \
  lang/src/core_eval.mo \
  lang/src/typecheck/meta_eval.mo \
  lang/src/tests/core_eval_lang_tests.mo
