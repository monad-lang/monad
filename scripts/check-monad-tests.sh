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
# a handful of checker/codegen bugs). A GAP does not fail the sweep; an
# unrecognised compile failure does.
#
# Then the same binary CHECKS the same corpus, which is the one gate here
# that is not about tests: the pre-commit hook's `monad check` is the Rust
# host, so the self-hosted checker was never run over the corpus by CI at
# all. See the block below for the six known check-gap files and how their
# error counts are held fixed.
set -euo pipefail

# The 10 files the self-hosted runner cannot build a working driver for
# today. Each is a PRE-EXISTING backend bug -- none is a problem with the
# test file or with the runner -- and each stays covered by the Rust
# runner at the bottom of this script, so excluding it here costs no
# coverage. Five groups:
#
# 1. `llc` rejects the emitted IR with an ill-typed or forward-referenced
#    `icmp`. Two shapes, both in a user test's own body -- a `match` arm
#    that reads a struct field -- and neither in anything the driver
#    generates:
#
#      * "instruction forward referenced with type 'i64'": a `phi i64`
#        takes its value from an `icmp` that the emitter writes LATER in
#        the .ll text, so the reference points forward at a value whose
#        type the parser has not seen yet. The bad IR is one `phi` per
#        file (`position.mo`'s `%t31 = phi i64 [%t29, %merge_8]` with
#        `%t29 = icmp` 11 lines further down; `parser.mo`'s
#        `%t13321`/`%t13319`, use 11 lines before its def).
#
#      * "'%tN' defined with type 'i1' but expected 'i64'": the LIFTED
#        LAMBDA case of this is FIXED (a lambda's own `ret` now goes
#        through the same `materialize_branch_val` /
#        `materialize_terminal_ret` pair a def body does), but the same
#        missing boxing is still reachable one path over, in a DEF's own
#        terminal merge block: `position::loc_eq_opt` ends in `merge_22`
#        with `%t69 = icmp eq i64 %t63, %t68` followed by `ret i64
#        %t69`. Note the function boxes the SAME shape everywhere else
#        (`%t70 = zext i1 %t69 to i64`): only the terminal-merge `ret`
#        misses it.
#
#    Diagnosed with a 20-line IR scan (icmp temps used later in an
#    `i64` position, with the use/def line numbers): 16 hits in
#    `position.mo`, 1 in `parser.mo`, 0 in the file that group 5 moved
#    here -- i.e. the scan reproduces exactly what `llc` reports, so it
#    is a usable progress oracle for this bug.
#        lang/src/parser/position.mo
#
# 2. Still no working driver, but no longer one bug -- three of this
#    group's four bugs are now closed:
#
#      * the `BEq_List_A_beq` dictionary doubling that used to be the
#        whole of this group is FIXED (the checker's own D4 rewrite is no
#        longer re-applied by the codegen class-call pass), which took
#        `cli/src/tests/main_tests.mo` and `std/src/list_tests3b.mo` off
#        this list entirely (17/17 and 5/5 self-hosted) and turned three
#        files from a dead driver into real, non-crashing test FAILURES:
#        `lang/src/core_eval.mo` 15/17, `lang/src/typecheck/meta_eval.mo`
#        2/4, `lang/src/tests/core_eval_lang_tests.mo` 6/7.
#
#      * `llc` used to reject the emitted IR ("'%tN' defined with type
#        'i1' but expected 'i64'"), because a LIFTED LAMBDA whose body is
#        a native comparison returned a raw `i1` from an `i64` function
#        -- `compile_db_lam_ir` appended `ret val_r` without the boxing
#        the top-level def path already applies. Measured at the time in
#        the IR: `lambda_69` = `icmp eq i64 %p1, 9; ret i64 %t164`,
#        reached from `list::test_find_by_missing`'s `List.find_by (fn x
#        => x == 9)`. A lifted lambda's own `ret` now goes through the
#        same `materialize_branch_val` / `materialize_terminal_ret` pair
#        a def body does, which took `std/src/list.mo` off this list
#        entirely (13/13 self-hosted).
#
#    What remains:
#
#      * driver dies by signal, for a cause other than the dict doubling
#        -- the emitted `BEq_List_A_beq` calls are arity-3 and correct
#        now, and two of the three contain no `BEq_List_A_beq` call at
#        all (measured after the fix, same signal before and after):
#        std/src/list_tests3a.mo
#        std/src/array.mo
#        examples/iteration_advanced.mo
#
#      * the three real test failures named above (each is its own bug;
#        they keep this list until their own file is green).
#
# 3. Unbounded allocation -- OOM-killed at ~30 GB RSS, no progress in 10
#    minutes under a 4 GB cap, while its 41 tests pass in milliseconds on
#    the host. The no-free-runtime memory pathology
#    (plans/bootstrapping/rung3-oom-no-free-runtime.md). EXCLUDED FOR THE
#    RUNNER'S SAKE, not just for speed: 30 GB disturbs everything else on
#    a CI machine.
#        lang/src/toml.mo
#
# 4. Same `llc` forward-reference family as group 1, newly EXPOSED (not
#    newly caused): lang/src/parser.mo used to be refused outright by
#    the runner's 255-test exit-code ceiling, so it never reached `llc`.
#    The result-file channel removed that ceiling, and the file's first
#    actual driver compile hits group 1's phi-vs-icmp block ordering
#    (a `match` arm reading a struct field, same shape as
#    position.mo's). Stays here with group 1 until that one bug is
#    fixed; its 288 tests remain covered by the Rust runner below.
#        lang/src/parser.mo
#
# 5. `llc` rejects the emitted IR ("use of undefined value
#    '@parse_democommand'"): the bare `derive_cli!` decl-macro's own
#    generated defs never reach codegen at all. The driver's IR holds
#    five `call i64 @parse_democommand(...)` and NO definition of it
#    under any name -- so this is not a qualification or mangling
#    mismatch but an absence, the same finding `cli/src/test_gaps.mo`
#    records for the `#[derive_cli]`/`#[derive]` family (P10). It used to
#    be recorded under group 1: `llc` hit an ill-typed `icmp` earlier in
#    the module and reported that first, and the lifted-lambda fix
#    removed it, exposing this. Coverage is unchanged either way -- the
#    Rust runner below still runs all five of the file's tests.
#        cli/src/tests/cli_derive_self_hosted_tests.mo
#
# ONE list, used by both the sweep and the Rust fallback -- they were two
# hand-maintained copies of the same paths, which is one edit away
# from a file that runs in neither.
host_only=(
  lang/src/parser/position.mo
  cli/src/tests/cli_derive_self_hosted_tests.mo
  std/src/list_tests3a.mo
  std/src/array.mo
  examples/iteration_advanced.mo
  lang/src/toml.mo
  lang/src/parser.mo
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
  std/src/base.mo
  std/src/derive_tests.mo
  std/src/map_tests.mo
  std/src/test_map_full.mo
  std/src/concurrent/combine_test.mo
  lang/src/json.mo
  cli/src/tests/cli_derive_tests.mo
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

# The self-hosted `check` over the SAME corpus (plus `bench`, which has no
# tests to sweep but is source like any other): the sweep above proves
# each file's tests RUN, this proves each file TYPECHECKS under the
# checker the shipped compiler actually uses. The pre-commit hook's
# `monad check` is the RUST host -- a different implementation -- so
# neither gate covers the other, and until this ran, nothing in CI used
# the self-hosted checker on the whole corpus. 180 files, ~52s.
#
# Six files fail it today, and all six are already registered in
# `cli/src/test_gaps.mo` (their test-side failures):
#
#   cli/src/tests/cli_derive_tests.mo  `#[derive_cli]` expands to nothing
#                                      -> `unknown variable
#                                      'parse_democommand'`, 7x
#   examples/derive.mo                 `#[derive]` is not supported by the
#                                      self-hosted parser
#   examples/structs.mo                a def's own named-call defaults do not
#                                      survive the parser
#   lang/src/json.mo                   the call's own ascription is
#                                      discarded by the self-hosted parser
#   std/src/concurrent/combine_test.mo the argument's own ascription is
#                                      discarded
#   std/src/derive_tests.mo            a macro-derived instance is invisible
#                                      to the class-call pass
#
# Excluding by path alone would hide a NEW check failure in any of them,
# so each carries its measured error COUNT: a file whose count changes
# fails this script even though its path is listed. Anything failing that
# is not on this list fails it too. The whole list should disappear with
# its registry entries (P9/P10 close four of the six).
check_gap_files=(
  cli/src/tests/cli_derive_tests.mo:7
  examples/derive.mo:1
  examples/structs.mo:1
  lang/src/json.mo:3
  std/src/concurrent/combine_test.mo:1
  std/src/derive_tests.mo:1
)

check_targets=()
while IFS= read -r f; do
  check_targets+=("$f")
done < <(find init std examples lang cli llvm runtime motes slow_tests bench -name '*.mo' | sort)

check_log="$out/check.log"
if "$out/monad" check "${check_targets[@]}" > "$check_log" 2>&1; then
  check_fails=0
else
  check_fails=$(grep -cE '^FAIL ' "$check_log" || true)
fi
check_bad=0
while IFS= read -r line; do
  path="${line#FAIL}"; path="${path#"${path%%[! ]*}"}"; path="${path%% (*}"
  count="${line#*\(}"; count="${count%% *}"
  want=""
  for entry in "${check_gap_files[@]}"; do
    case "$entry" in "$path:"*) want="${entry##*:}" ;; esac
  done
  if [ -z "$want" ]; then
    echo "self-hosted check: UNEXPECTED failure -- $line" >&2
    check_bad=1
  elif [ "$want" != "$count" ]; then
    echo "self-hosted check: $path now reports $count error(s), recorded $want" >&2
    check_bad=1
  fi
done < <(grep -E '^FAIL ' "$check_log" || true)
if [ "$check_bad" != 0 ]; then
  cat "$check_log" >&2
  exit 1
fi
echo "self-hosted check: ${check_fails} known check-gap file(s), counts unchanged"

# Everything the self-hosted runner could not run, through the Rust
# runner, so each file stays covered and a real regression in any of them
# still fails this script.
cargo run --release -- test "${host_only[@]}" "${gap_files[@]}"
