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
# Two runners, one corpus. Every .mo file is tested by exactly one of
# them, and none is left untested by both: the SELF-HOSTED runner takes
# the whole corpus except `host_only` below, and the RUST runner takes
# `host_only` plus any file the self-hosted runner reports as a GAP
# (`cli/src/test_gaps.mo` -- unwired f64 natives, the async runtime, and
# two codegen bugs). A GAP does not fail the sweep; an unrecognised
# compile failure does.
set -euo pipefail

# The 13 files the self-hosted runner cannot build a working driver for
# today. Each is a PRE-EXISTING backend bug -- none is a problem with the
# test file or with the runner -- and each stays covered by the Rust
# runner at the bottom of this script, so excluding it here costs no
# coverage. Four groups:
#
# 1. `llc` rejects the emitted IR ("instruction forward referenced with
#    type 'i64'"): an `icmp` result reaches a `phi i64` from a block
#    emitted after its own use. The bad IR is in a user test's own body
#    -- a `match` arm that reads a struct field -- not in anything the
#    driver generates.
#        lang/src/parser/position.mo
#        cli/src/tests/cli_derive_self_hosted_tests.mo
#
# 2. The driver dies by signal. In the emitted `BEq_List_A_beq` the
#    recursive tail comparison applies the ELEMENT dictionary to two
#    lists, dereferencing list cells as scalars.
#        cli/src/tests/main_tests.mo
#        std/src/list_tests3a.mo
#        std/src/list_tests3b.mo
#        std/src/array.mo
#        examples/iteration_advanced.mo
#        std/src/list.mo
#        lang/src/core_eval.mo
#        lang/src/typecheck/meta_eval.mo
#        lang/src/tests/core_eval_lang_tests.mo
#
# 3. Unbounded allocation -- OOM-killed at ~30 GB RSS, no progress in 10
#    minutes under a 4 GB cap, while its 34 tests pass in milliseconds on
#    the host. The no-free-runtime memory pathology
#    (plans/bootstrapping/rung3-oom-no-free-runtime.md). EXCLUDED FOR THE
#    RUNNER'S SAKE, not just for speed: 30 GB disturbs everything else on
#    a CI machine.
#        lang/src/toml.mo
#
# 4. More tests than a driver's 8-bit exit code can report (288 > 255),
#    so the runner refuses it by design -- see the guard in
#    cli/src/main.mo. Not a bug to fix here; the file needs splitting, or
#    the driver needs a richer result channel than an exit code.
#        lang/src/parser.mo
#
# ONE list, used by both the sweep and the Rust fallback -- they were two
# hand-maintained copies of the same 13 paths, which is one edit away
# from a file that runs in neither.
host_only=(
  lang/src/parser/position.mo
  cli/src/tests/cli_derive_self_hosted_tests.mo
  cli/src/tests/main_tests.mo
  std/src/list_tests3a.mo
  std/src/list_tests3b.mo
  std/src/array.mo
  examples/iteration_advanced.mo
  lang/src/toml.mo
  lang/src/parser.mo
  std/src/list.mo
  lang/src/core_eval.mo
  lang/src/typecheck/meta_eval.mo
  lang/src/tests/core_eval_lang_tests.mo
)

# The files the self-hosted runner reports as GAPs (cli/src/test_gaps.mo).
# Handed to the Rust runner for the same reason `host_only` is: a gap
# means those tests do not run self-hosted, and a test that runs nowhere
# is worse than one that runs slowly. This list is expected to shrink to
# nothing alongside cli/src/test_gaps.mo itself.
gap_files=(
  init/src/optics_tests.mo
  examples/optics.mo
  std/src/concurrent/fiber_test.mo
  init/src/tests.mo
  std/src/sha256_tests.mo
  init/src/foldable_tests.mo
  init/src/foldable_tests_fold.mo
  std/src/base.mo
  std/src/derive_tests.mo
  std/src/list_tests1.mo
  std/src/list_tests2.mo
  std/src/map_tests.mo
  std/src/test_map_full.mo
  lang/src/codegen/test/compile_tests.mo
  lang/src/codegen/test/e2e_typecheck_tests.mo
  std/src/sha256.mo
  std/src/concurrent/combine_test.mo
  lang/src/codegen/test/test_e2e.mo
  lang/src/codegen/test/test_link_e2e.mo
  lang/src/json.mo
  cli/src/tests/cli_derive_tests.mo
  examples/test_mote.mo
  examples/derive.mo
  examples/structs.mo
  examples/indexed_monads.mo
  examples/state_monad.mo
)

out="${TMPDIR:-/tmp}/monad-bootstrap-ci"
# Staleness: every input that ends up INSIDE the binary. `init` and `std`
# are compiled into it just as `lang`/`cli`/`llvm`/`runtime` are, and
# runtime.c/.h are linked into it -- omitting them meant an edit to any
# of them left a stale binary in place, so CI tested the previous
# compiler and reported its results as this commit's.
if [ ! -x "$out/monad" ] || [ -n "$(find init std lang cli llvm runtime \
      \( -name '*.mo' -o -name '*.c' -o -name '*.h' \) \
      -newer "$out/monad" -print -quit)" ]; then
  mkdir -p "$out"
  cargo run --release -- run cli/src/main.mo compile cli/src/main.mo -o "$out/monad" --release
fi
test -x "$out/monad"

# The self-hosted sweep: the whole corpus except `host_only`. Those files
# sit in directories with many healthy files, so they are named
# individually rather than by pruning their parent directory.
self_hosted_targets=()
while IFS= read -r f; do
  for skip in "${host_only[@]}"; do
    if [ "$f" = "$skip" ]; then
      continue 2
    fi
  done
  self_hosted_targets+=("$f")
done < <(find init std examples lang cli llvm runtime motes slow_tests -name '*.mo' | sort)

"$out/monad" test "${self_hosted_targets[@]}"

# Everything the self-hosted runner could not run, through the Rust
# runner, so each file stays covered and a real regression in any of them
# still fails this script.
cargo run --release -- test "${host_only[@]}" "${gap_files[@]}"
