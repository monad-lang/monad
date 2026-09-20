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
# (`cli/src/test_gaps.mo` -- the async runtime, and a handful of
# checker/codegen bugs). A GAP does not fail the sweep; an
# unrecognised compile failure does.
#
# Then the same binary CHECKS the same corpus, which is the one gate here
# that is not about tests: the pre-commit hook's `monad check` is the Rust
# host, so the self-hosted checker was never run over the corpus by CI at
# all. See `check_gap_files` below for the known check-gap files and how
# their error counts are held fixed (the count is deliberately not
# repeated here -- it went stale the first time the list changed).
set -euo pipefail

# The 5 files the self-hosted runner cannot build a working driver for
# today. Each is a PRE-EXISTING backend bug -- none is a problem with the
# test file or with the runner -- and each stays covered by the Rust
# runner at the bottom of this script, so excluding it here costs no
# coverage. Four groups:
#
# This list was 10 entries when P10 landed. Five of the ten had stopped
# being true, and were re-measured file by file on 2026-09-19: each flip
# is recorded at the group it left. Removing an entry whose file now
# PASSES is as load-bearing as removing a stale GAP -- a file left here
# silently loses its self-hosted coverage, and the Rust runner (a
# different implementation) is what tests it instead.
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
#    `position.mo`, 1 in `parser.mo`, 0 in the file group 5's closed note
#    is about -- i.e. the scan reproduces exactly what `llc` reports, so
#    it is a usable progress oracle for this bug.
#        lang/src/parser/position.mo
#
# 2. Driver dies by signal, for a cause other than the dict doubling --
#    and nothing else is left of this group. Two of its four bugs closed
#    earlier (`BEq_List_A_beq`'s dictionary doubling, a checker D4
#    rewrite the codegen class-call pass re-applied; and a lifted
#    lambda's unboxed `ret`), and the rest closed with P8/P10, measured
#    again on 2026-09-19:
#
#      * the `BEq_List_A_beq` dictionary doubling that used to be the
#        whole of this group is FIXED (the checker's own D4 rewrite is no
#        longer re-applied by the codegen class-call pass), which took
#        `cli/src/tests/main_tests.mo` and `std/src/list_tests3b.mo` off
#        this list entirely (17/17 and 5/5 self-hosted) and turned three
#        files from a dead driver into real, non-crashing test FAILURES:
#        `lang/src/core_eval.mo` 15/17, `lang/src/typecheck/meta_eval.mo`
#        2/4, `lang/src/tests/core_eval_lang_tests.mo` 6/7. Those three
#        are GREEN now -- 17/17, 4/4, 7/7 -- so they left this list too,
#        and the sweep runs their tests through the shipped runner
#        instead of the Rust one.
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
#      * `examples/iteration_advanced.mo` was the third file on this
#        group's signal list; it is 6/6 self-hosted now and has left it.
#
#    What remains -- the same signal, still unexplained, and the emitted
#    `BEq_List_A_beq` calls are arity-3 and correct (measured after the
#    fix, same signal before and after):
#        std/src/list_tests3a.mo
#        std/src/array.mo
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
# Group 5 (CLOSED, entry removed). `llc` used to reject the emitted IR
#    with "use of undefined value '@parse_democommand'": the bare
#    `derive_cli!` decl-macro's own generated defs never reached codegen
#    at all -- the driver's IR held five `call i64 @parse_democommand(...)`
#    and NO definition of it under any name, an absence rather than a
#    mangling mismatch, which is the same finding `cli/src/test_gaps.mo`
#    recorded for the `#[derive_cli]`/`#[derive]` family. The bridge that
#    closed that family (P10, 707bbd7) closes this one: re-measured, the
#    file is 5/5 self-hosted, so it has left `host_only` and the sweep
#    now runs its tests through the shipped runner.
#
# ONE list, used by both the sweep and the Rust fallback -- they were two
# hand-maintained copies of the same paths, which is one edit away
# from a file that runs in neither.
host_only=(
  lang/src/parser/position.mo
  std/src/list_tests3a.mo
  std/src/array.mo
  lang/src/toml.mo
  lang/src/parser.mo
)

# The files the self-hosted runner reports as GAPs (cli/src/test_gaps.mo).
# Handed to the Rust runner for the same reason `host_only` is: a gap
# means those tests do not run self-hosted, and a test that runs nowhere
# is worse than one that runs slowly. This list is expected to shrink to
# nothing alongside cli/src/test_gaps.mo itself -- the f64 family
# (`init/src/optics_tests.mo`, `examples/optics.mo`, `std/src/base.mo`)
# left it when P9 wired the backend, so those three now run self-hosted
# (11/11, 9/9 and 45/45) and are passed to the RUST runner no longer.
# The `#[derive]` family went the same way in P10: an attribute on a
# `struct` decl, the attribute-to-macro bridge, and the struct-ctor
# arity entry together take `std/src/derive_tests.mo` (22/22),
# `cli/src/tests/cli_derive_tests.mo` (7/7) and `examples/derive.mo`
# (7/7) off it.
gap_files=(
  std/src/concurrent/fiber_test.mo
  init/src/tests.mo
  std/src/concurrent/combine_test.mo
  lang/src/json.mo
  examples/structs.mo
  examples/indexed_monads.mo
  examples/state_monad.mo
  # Qualified references in TARGET position do not resolve self-hosted:
  # the flatten drops each decl's owning module, so the pair match
  # cannot succeed across a module boundary (see cli/src/test_gaps.mo
  # for the full reason). The Rust runner below still runs all four of
  # its tests, and the DEPENDENCY-position half of the feature works.
  std/src/qualified_ref_tests.mo
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
# Three files fail it today, and all three are already registered in
# `cli/src/test_gaps.mo` (their test-side failures):
#
#   examples/structs.mo                a def's own named-call defaults do not
#                                      survive the parser
#   lang/src/json.mo                   the call's own ascription is
#                                      discarded by the self-hosted parser
#   std/src/concurrent/combine_test.mo the argument's own ascription is
#                                      discarded
#
# The `#[derive]` trio that headed this list left it with P10, and the
# comment on `gap_files` above records what closed them -- all three now
# report 0 errors (`cli/src/tests/cli_derive_tests.mo` was 7,
# `examples/derive.mo` and `std/src/derive_tests.mo` 1 each).
# `std/src/derive_tests.mo`'s own entry survived that commit even though
# by then the file reported 0 errors, and is removed here, in lockstep
# with the flip: an entry left behind for a file that has become clean is
# exactly what would excuse a NEW failure in it, since this list is
# matched by path first, count second. Measured before removing: `monad
# check std/src/derive_tests.mo` -> 0 error(s), and the corpus-wide check
# log holds no `FAIL` line for it.
#
# Excluding by path alone would hide a NEW check failure in any of them,
# so each carries its measured error COUNT: a file whose count changes
# fails this script even though its path is listed. Anything failing that
# is not on this list fails it too. The whole list should disappear with
# its registry entries.
check_gap_files=(
  examples/structs.mo:1
  lang/src/json.mo:3
  std/src/concurrent/combine_test.mo:1
  # Same cause as its `gap_files` entry: a qualified reference in TARGET
  # position cannot resolve self-hosted, because the flatten drops each
  # decl's owning module (see cli/src/test_gaps.mo for the full reason).
  # Two of its four tests use one; the other two resolve through the
  # target's own module and check clean.
  std/src/qualified_ref_tests.mo:2
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
