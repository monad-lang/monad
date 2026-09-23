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
# ONE runner, one corpus: the self-hosted runner tests every .mo file in it
# and there is ONE total to read. That is where the mechanism was always
# headed, and Phase 12 finished it -- the Rust fallback at the tail of this
# script, the `gap_files` array that fed it, and the `cli/src/test_gaps.mo`
# registry that filled that array are all deleted.
#
# The record of how it got here is kept, because each stage names the fix
# that closed it. There were once TWO runners and every .mo file was tested
# by exactly one of them: the SELF-HOSTED runner took the whole corpus
# except `host_only` below, and the RUST runner took `host_only` plus any
# file the self-hosted runner reported as a GAP (the async runtime, and a
# handful of checker/codegen bugs). A GAP did not fail the sweep; an
# unrecognised compile failure did. Both lists emptied before they were
# deleted: `host_only`'s last entry (`lang/src/toml.mo`) left with the fix
# recorded at group 3 below, and `gap_files`' last two left with Phase 8's
# async runtime, which is what they were waiting for.
#
# Then the same binary CHECKS the same corpus, which is the one gate here
# that is not about tests: the pre-commit hook's `monad check` is the Rust
# host, so the self-hosted checker was never run over the corpus by CI at
# all. See `check_gap_files` below for the known check-gap files and how
# their error counts are held fixed (the count is deliberately not
# repeated here -- it went stale the first time the list changed).
set -euo pipefail

# `host_only`: the files the self-hosted runner could not build a working
# driver for. It is EMPTY and stays declared, because the skip loop below
# reads it -- every entry it ever held was a PRE-EXISTING backend bug,
# never a problem with the test file or with the runner, and while one was
# listed the Rust runner at the bottom of this script covered it, so
# excluding it here cost no coverage. That fallback is gone as of Phase
# 12, so a live entry here would now cost real coverage.
#
# This list was 10 entries when P10 landed, 5 before Phase 5 and 3 before
# Phase 6. Five of the ten had stopped being true and were re-measured
# file by file on 2026-09-19, the two group-1/group-4 entries went on
# 2026-09-21, and group 2's two went on 2026-09-22; each flip is recorded
# at the group it left. Removing an entry whose file now PASSES is as
# load-bearing as removing a stale GAP -- a file left here silently loses
# its self-hosted coverage, and with the Rust fallback deleted there is
# now nothing behind it at all.
#
# 1. (CLOSED, both entries removed.) `llc` rejected the emitted IR with
#    an ill-typed or forward-referenced `icmp`, in two shapes that turned
#    out to be ONE emit defect with three faces, all in `emit.mo`:
#
#      * "instruction forward referenced with type 'i64'": a `phi i64`
#        took its value from an `icmp` the emitter wrote LATER in the .ll
#        text. Not a boxing gap at all -- a DOMINANCE-ORDER one: both
#        `compile_match_ir` and `build_merge_result` emitted the merge
#        block (whose `phi` operands are the branch/case values) BEFORE
#        the blocks those values are defined in. LLVM tolerates a forward
#        reference only when the use site's stated type matches the
#        definition's, which is exactly why only the `icmp`-produced
#        cases ever failed loudly. Both now emit merge LAST, in strict
#        dominance order (entry blocks, branches, their nested blocks,
#        merge).
#
#      * "'%tN' defined with type 'i1' but expected 'i64'": the same
#        merge block's `phi` operand for an ALREADY-TERMINATED arm body.
#        `materialize_branch_val` deliberately skips such a body (its own
#        block already `ret`s the value directly, per `compose_seq`'s
#        convention), so the raw `icmp` reached the `phi` unboxed.
#        `materialize_terminal_ret` handled that shape for the two `ret`
#        paths only; it now also returns the boxed value, and the `phi`
#        paths (`build_match_case_block`, `build_db_if_blocks`) call it
#        before `retarget_terminal_ret` and use its result.
#
#      * A third face, same class, in the ARGUMENT path: the
#        `let`-binding and both accumulated-argument sites
#        (`compile_ntv_args_go`, `compile_spine_args_go`) blind-appended
#        the materialization instructions after a fragment that could
#        already end in a terminator. All three now splice via
#        `compose_seq_acc`.
#
#    Re-measured 2026-09-21 with the self-hosted runner: `position.mo`
#    10/10 and `parser.mo` 291/291, so the group-4 entry below left with
#    this one -- the two were always the same bug, recorded twice because
#    the second only became reachable once the runner's old 255-test
#    exit-code ceiling was gone.
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
#    CLOSED 2026-09-22, both entries removed. The signal was a dictionary
#    in the WRONG SLOT, and it survived the earlier `BEq_List_A_beq` fix
#    because a different search picks that slot:
#    `resolve_ordinary_constrained_call` has no instance head of its own,
#    so it passes `bindings = List.empty` to `constraint_carriers`, which
#    then answers `[carrier]` -- the WHOLE carrier. Resolving `[BEq A]` at
#    `List I64` re-matches `instance [BEq A] BEq (List A)`, and a dict name
#    is mangled from the INSTANCE's declared args, so the element slot of a
#    `List I64` comparison received `__Dict_BEq_List_A` and the driver read
#    a raw `I64` in `monad_get_tag`. `find_constraint_bound_carrier_any`
#    (`lang/src/scope.mo`) now resolves the constraint at the carrier the
#    matched instance's own head BINDS the constraint's variable to
#    (`A := I64`), so the element slot gets `__Dict_BEq_I64`.
#
#    Measured before removing them, with a binary rebuilt from the fix:
#    `std/src/list_tests3a.mo` 7/7 (was `driver exited -1`) and
#    `std/src/array.mo` 16/16, with no pre-fix PASS lost anywhere in the
#    sweep. Two screens an earlier attempt added for this same crash were
#    measured INERT and are removed again rather than left in on a
#    falsified theory: one on whether a candidate PINS the matched
#    instance's own variables, and a REFUSAL of a placeholder candidate in
#    `infer_carrier_type`.
#
#    `init/src/foldable_tests.mo` and `init/src/foldable_tests_fold.mo` DID
#    briefly lose their `Foldable.foldr (fn x acc => x + acc) 0 [] == 0`
#    test to this work, and the refusal was NOT the cause -- reverting it
#    left them failing, and a symbol-table reading of the session's own
#    build artifacts (the wrap-only build has `registered_def_type` and
#    none of this phase's other new defs) put the blame on the def-type
#    CHANNEL: `collect_def_types` now registers every def type
#    `elaborate_def`-wrapped, and the arm of `infer_carrier_type` that reads
#    a bare HEAD off that value -- the 0-arg def-reference arm, whose own
#    comment names the promoted `FromListLiteral_List_empty` as its
#    load-bearing case -- reads nothing off a `forall`, so the bare `[]`
#    literal answered no carrier at all and the enclosing `Foldable.foldr`
#    reported `no instance found`. Measured on the wrap-only build: the bare
#    `[]` fails, while `([] : List I64)`, a typed `let`, `List.empty`,
#    `[1, 2, 3]` and a bare `none` all pass -- the empty list was the one
#    arm the wrap could break. It now unquantifies first (`strip_foralls`),
#    which is byte-for-byte the raw-type behavior that arm had before the
#    wrap.
#
# 3. (CLOSED, entry removed.) Recorded as "Unbounded allocation -- OOM-killed
#    at ~30 GB RSS, no progress in 10 minutes under a 4 GB cap", and blamed on
#    the no-free-runtime pathology. RE-MEASURED 2026-09-22 and the recorded
#    cause was WRONG in a way that mattered: this file never allocated its way
#    out of memory. Under `systemd-run --scope -p MemoryMax=4G` it burned the
#    full 60s timeout at a FLAT 2.5 MB RSS and 98.7% CPU -- a spin, not a
#    blowup. (`exit 137` is BOTH the OOM kill and the timeout kill; only the
#    RSS sample tells them apart.)
#
#    The emitted IR named it in one line: `test_parse_single_header`'s
#    `Map.lookup "mote" t` compiled to `std.map::Map_HashMap_lookup` while `t`
#    was a `BTreeMap String Toml.Value`, so HashMap's bucket walk read
#    BTreeMap nodes -- and `HashMap.lookup`'s own tail-recursive `lookup_loop`
#    is TCO'd, which is exactly why the heap stayed flat and the CPU did not.
#    The carrier had defaulted to `class Map (M : (K : Type) -> (V : Type) ->
#    Type := HashMap)` (`std/src/map.mo`): the call's map argument was a
#    match-arm binder over a CALL scrutinee, and `scrutinee_type_spine`
#    (`lang/src/scope.mo`) only looked a scrutinee up when it was a
#    `Term.var`. A call scrutinee yielded no spine, so the arm's binder never
#    got the matched constructor's declared field types substituted against
#    the scrutinee's concrete type args (`Result Toml.ParseError (BTreeMap
#    String Toml.Value)`) and the instance search had no carrier to match.
#
#    Why only this file, which the recorded prose guessed wrong: every other
#    test in the corpus reaches its lookup through `toml_table_lookup_eq`,
#    whose own parameter is typed `BTreeMap String Toml.Value`, so the
#    binder's carrier comes from the def's signature and never from a
#    scrutinee. Test 9 is the first INLINE lookup and test 14 the second. The
#    trigger is not "multi-line" and not "nested table"; it is an inline
#    `Map.lookup` whose map argument is a match-arm binder over a call
#    scrutinee.
#
#    Fixed by resolving a call scrutinee's return type through the same
#    def/ctor/local channel `infer_carrier_type`'s application arm already
#    used for call ARGUMENTS. Measured before removing: 41/41 through the
#    self-hosted runner in 4.8s (was 8 tests then a hang), and zero
#    `Map_HashMap_lookup` left in the file's emitted IR.
#
#    The 28 GB `check_deps=true` blowup (`lang/src/module.mo:1526`) is NOT
#    this cause, and this measurement does not decide it -- whatever that is,
#    the live-set-vs-rooting question stays open for the checker work.
#
# 4. (CLOSED, entry removed -- the same bug as group 1.) Same `llc`
#    forward-reference family, newly EXPOSED (not newly caused):
#    lang/src/parser.mo used to be refused outright by the runner's
#    255-test exit-code ceiling, so it never reached `llc`. The
#    result-file channel removed that ceiling, and the file's first
#    actual driver compile hit group 1's phi-vs-icmp block ordering (a
#    `match` arm reading a struct field, same shape as position.mo's).
#    With group 1 closed it runs 291/291 through the self-hosted runner.
#
# Group 5 (CLOSED, entry removed). `llc` used to reject the emitted IR
#    with "use of undefined value '@parse_democommand'": the bare
#    `derive_cli!` decl-macro's own generated defs never reached codegen
#    at all -- the driver's IR held five `call i64 @parse_democommand(...)`
#    and NO definition of it under any name, an absence rather than a
#    mangling mismatch, which is the same finding the deleted `cli/src/test_gaps.mo`
#    recorded for the `#[derive_cli]`/`#[derive]` family. The bridge that
#    closed that family (P10, 707bbd7) closes this one: re-measured, the
#    file is 5/5 self-hosted, so it has left `host_only` and the sweep
#    now runs its tests through the shipped runner.
#
# ONE list, read by the sweep's skip loop (and, until Phase 12, by the
# Rust fallback too) -- they were two hand-maintained copies of the same
# paths, which is one edit away from a file that runs in neither.
host_only=(
)

# The files the self-hosted runner reported as GAPs. THIS ARRAY IS DELETED
# as of Phase 12, together with the `cli/src/test_gaps.mo` registry that
# filled it and the Rust fallback it fed: the self-hosted runner covers the
# whole corpus alone, so there is nothing left to hand over. It was emptied
# before it was deleted, deliberately, because a path left here after its
# GAP had closed would have silently moved that file's coverage from the
# self-hosted runner to a different implementation's while gaining nothing.
#
# The record of what left it, kept because every entry names a fix:
#
# The f64 family (`init/src/optics_tests.mo`, `examples/optics.mo`,
# `std/src/base.mo`) left it when P9 wired the backend, so those three now
# run self-hosted (11/11, 9/9 and 45/45) and are passed to the RUST runner
# no longer. The `#[derive]` family went the same way in P10: an attribute
# on a `struct` decl, the attribute-to-macro bridge, and the struct-ctor
# arity entry together take `std/src/derive_tests.mo` (22/22),
# `cli/src/tests/cli_derive_tests.mo` (7/7) and `examples/derive.mo`
# (7/7) off it. `init/src/tests.mo` is the third to go: the last entry
# this list had for a DEAD DRIVER, and it was the only one ever listed
# for that wording. Its `some 1 == (List.get 0 [1, 2, 3])` shape sent the
# option instance's own dictionary into its ELEMENT slot and killed the
# driver with a signal, and it now runs 102/102 through the self-hosted
# runner (see cli/src/test_gaps.mo for both halves of the fix).
# `std/src/qualified_ref_tests.mo` left this list with Phase 3, in
# lockstep with its `check_gap_files` entry. A qualified reference in
# TARGET position could not resolve self-hosted because the flatten
# handed the whole decl list a SINGLE `ModulePath` -- the target's --
# so `build_scope_def` stamped every DEPENDENCY def with the CONSUMER's
# module, and `find_def_by_module_and_name` matches name AND module, so
# its pair match could never succeed across a boundary. The flatten now
# carries each decl's own owning module (`DeclGroup`, lang/src/types.mo)
# and the pair match compares RENDERED names, because a DECLARED name
# is one identifier with an embedded dot (`dotted_def_name` ->
# `Identifier.id`) while a ref's name half is split per dot into
# segments -- which is why the file's single-segment ref resolved and
# its dotted one did not. Measured before removing: 0 error(s) and 4/4
# through the self-hosted runner.
#
# The LAST TWO were both for the ASYNC natives, and they were the pair
# the whole registry was opened for: `std/src/concurrent/fiber_test.mo`
# (the unwired `fork_io`/`await_fiber`/`cancel_fiber` family) and
# `std/src/concurrent/combine_test.mo` (the same family's
# `scope_new`/`scope_fork`/`scope_drop`/`sleep_io`). Phase 8 built the
# runtime they were waiting for: one OS thread per fiber, with each
# handle's lifetime kept by the `_Atomic(int64_t)` refcount that every
# `monad_alloc`'d block already carries (`runtime/src/runtime.c`'s fiber
# and scope section). `combine_test.mo`'s CHECKER failure -- `no instance
# found for `Monad.bind`` -- had already closed with Phase 1, which is why
# the file stopped on the natives alone after that commit; both files were
# then measured through the self-hosted runner with a binary rebuilt from
# the change, and both report a clean run.
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

# The self-hosted sweep: the whole corpus except `host_only` (empty since
# `lang/src/toml.mo` left it -- see group 3 above). An excluded file sits
# in a directory with many healthy files, which is why the skip is a
# per-path compare rather than a pruned parent directory.
self_hosted_targets=()
while IFS= read -r f; do
  for skip in "${host_only[@]}"; do
    if [ "$f" = "$skip" ]; then
      continue 2
    fi
  done
  self_hosted_targets+=("$f")
done < <(find init std examples lang cli llvm runtime motes slow_tests -name '*.mo' | sort)

self_hosted_rc=0
"$out/monad" test "${self_hosted_targets[@]}" || self_hosted_rc=$?
if [ "$self_hosted_rc" -ne 0 ]; then
  # Deliberately NOT fatal: `set -e` used to abort here, which dropped the
  # whole check phase (and, before Phase 12, the Rust fallback) whenever a
  # single test failed -- so a red sweep reported one total and no
  # `self-hosted check:` line, indistinguishable from a truncated run.
  # The status is re-raised at the end of the script.
  echo "self-hosted tests FAILED (exit $self_hosted_rc) -- the check phase still runs"
fi

# The self-hosted `check` over the SAME corpus (plus `bench`, which has no
# tests to sweep but is source like any other): the sweep above proves
# each file's tests RUN, this proves each file TYPECHECKS under the
# checker the shipped compiler actually uses. The pre-commit hook's
# `monad check` is the RUST host -- a different implementation -- so
# neither gate covers the other, and until this ran, nothing in CI used
# the self-hosted checker on the whole corpus. 180 files, ~52s.
#
# `std/src/qualified_ref_tests.mo` was the last file on it and left with
# Phase 3, in lockstep with its `gap_files` entry -- that array is now
# deleted, and its entry recorded the cause and the fix. Measured before removing: `monad check
# std/src/qualified_ref_tests.mo` -> 0 error(s), and the corpus-wide
# check log holds no `FAIL` line for it.
#
# `examples/structs.mo` left this list with Phase 2, in the same commit
# as its `gap_files` entry (since deleted): a def's own declared `:=`
# defaults now reach
# the checker, so its one error -- `named call: missing required field
# `factor`` -- is gone. Measured before removing: the file reports 0
# error(s) and runs 10/10 through the self-hosted runner.
#
# `lang/src/json.mo` (3 errors) and `std/src/concurrent/combine_test.mo`
# (1) left this list with Phase 1's expected-type channel, together with
# their `gap_files` entries (since deleted): both were the checker half of
# the SAME
# missing channel -- a def call's return type was never solved against
# the ambient expected type, so `IO.pure (List.empty : List I64)` came
# back as its signature's raw, unsolved `IO A`. Measured before removing
# them, with a binary rebuilt from the fix: `monad check
# lang/src/json.mo std/src/concurrent/combine_test.mo` -> both `ok`, 0
# error(s) each.
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
# is not on this list fails it too.
#
# The list is now EMPTY, which is what the whole mechanism was for: the
# `UNEXPECTED failure` arm below is the only one that can fire, so the
# corpus-wide self-hosted check is a hard gate and any file that starts
# failing it fails CI. The loop and the count check stay until Phase 12
# deletes the scaffolding outright -- an empty registry is not the same
# thing as no registry, and the deletion is its own reviewed step.
check_gap_files=(
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

# The Rust fallback ran here: everything the self-hosted runner could not
# run went through it, so each file stayed covered and a real regression in
# any of them still failed this script. There is nothing left for it to
# cover -- both lists are empty and the registry that filled them is
# deleted -- so Phase 12 deleted the call and kept its message below.
#
# Both lists are empty, so there is nothing to hand over -- and the call
# has to be SKIPPED rather than made with empty arrays: bare `monad test`
# is not a no-op, it is a different mode (it resolves the mote containing
# the working directory and tests that), so passing it no paths would run
# a second, unintended sweep instead of nothing. That guard was deleted in
# Phase 12 along with the fallback: with both lists empty the guard had no
# work left but to hold the message, and the message is what the sweep
# asserts below.
echo "rust runner: no files left -- the self-hosted runner covers the corpus alone"

# Re-raise the captured self-hosted status: without this the `|| self_hosted_rc=$?`
# above would turn a red run into an exit 0, which is worse than the abort it
# replaced. A bad check phase has already exited 1 by now.
exit "$self_hosted_rc"
