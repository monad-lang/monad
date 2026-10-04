#!/usr/bin/env bash
# The full .mo test sweep, run by `tasks."monad:test"` in devenv.nix
# (which CI's `compiler-checks` job invokes, from
# scripts/ci-compiler-checks.sh). prek does not invoke a shell, so a
# hook entry cannot chain commands -- hence this wrapper script.
#
# Runs the SELF-HOSTED test runner (`monad test`, implemented in
# lang/src/codegen/test_driver.mo + cli/src/main.mo), not the Rust
# evaluator: that runner is what the project ships, and until this
# switched, nothing in CI exercised it over the whole corpus. It
# compiles a driver binary per test file and runs it, so a test failure
# here is a failure of real compiled code.
#
# The binary has to be built in this job: actions/checkout runs git
# clean -ffdx at the start of every job, wiping target-rust/, target-monad/,
# .devenv/ and the config, so no job and no run inherits a compiler. The two
# halves of `compiler-checks` DO share this checkout's scratch directory, on
# purpose -- the sweep's compiler IS the ladder's release rung-1
# (scripts/ci-compiler-checks.sh) -- and what keeps that from being a race is
# that the ladder writes that path and this script only reads it. The staleness
# check and build command live in
# scripts/build-self-hosted.sh, shared with the other two CI scripts:
# reuse an existing binary, but rebuild when any source compiled INTO
# it is newer, since a stale compiler reports failures that are really
# its own age. All four motes, not just lang/: cli/ holds the compile
# target, llvm/ and runtime/ the backend.
#
# `MONAD_BIN` replaces that build when the caller already has the compiler.
# CI's `compiler-checks` job points it at the LADDER's own release rung-1
# (`<checkout>/target-monad/bootstrap-ci/monad`, scripts/lib/bootstrap-dir.sh):
# the ladder builds that binary from this commit's tree on every compiler
# change, and handing it to the sweep is what makes one interpretation do two
# jobs -- the sweep starts the moment the binary is finished instead of after
# the ladder has also checked and turned over, and nothing builds a second copy
# of the same compiler from the same tree (scripts/ci-compiler-checks.sh). What
# MONAD_BIN replaces is still the interpreter's ~5 minute turn; with the
# ladder's binary there is no cargo build in this job to remove, and the flake
# package was the thing that used to supply both.
#
# `packages.monad` is graded instead by the `flake-package` job, on the changes
# that can move it (`nix/**`, `flake.nix`, `flake.lock`) -- it links rung 1
# rather than re-interpreting the tree, so for its own inputs it is a store hit.
# MONAD_BIN is the repo's existing
# name for "the self-hosted compiler to run" (scripts/check-docs.sh,
# tools/debug_transparency_oracle.sh); build-self-hosted.sh's own header says
# why the HOST override it takes is spelled differently.
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
# all. This is now a HARD gate with no registry behind it: `check_gap_files`
# allowed a listed file to fail with a recorded error count, that array is
# deleted as of Phase 13, and every `FAIL` line fails the script. The count
# that used to be held fixed per path is gone with it -- it was the thing
# that went stale the first time the list changed.
set -euo pipefail

# Everything below resolves paths against the repository root: the build
# helper by relative path, and the sweep's own `find` lists by bare tree
# name. A `find` run from the wrong directory yields an empty sweep rather
# than an error, so the cwd is not left to the caller -- the three sibling
# scripts all cd here themselves, and CI happens to invoke every one of
# them from the repo root.
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

# `host_only`: the files the self-hosted runner could not build a working
# driver for. Every entry it ever held was a PRE-EXISTING backend bug,
# never a problem with the test file or with the runner, and while one was
# listed the Rust runner at the bottom of this script covered it, so
# excluding it here cost no coverage. That fallback is gone as of Phase
# 12 and the ARRAY is gone as of Phase 13, so its record is all that is
# left -- with nothing reading it, a live entry could only have cost real
# coverage while looking like a maintained exclusion.
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
# The list itself is DELETED as of Phase 13, for the reason `gap_files`
# went in Phase 12: it had been empty since `lang/src/toml.mo` left it
# (group 3 above), and an empty array whose only reader is a skip loop is
# not the same thing as no array -- repopulating it would silently move a
# file's coverage off the self-hosted runner while gaining nothing, and
# this branch's history is largely a list of exclusions that outlived
# their causes. The record above is kept, because every entry names a fix.

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
# `motes/clap/src/tests/cli_derive_tests.mo` (7/7) and `examples/derive.mo`
# (7/7) off it. `init/src/tests.mo` is the third to go: the last entry
# this list had for a DEAD DRIVER, and it was the only one ever listed
# for that wording. Its `some 1 == (List.get 0 [1, 2, 3])` shape sent the
# option instance's own dictionary into its ELEMENT slot and killed the
# driver with a signal, and it now runs 102/102 through the self-hosted
# runner. The fix has two halves, both required, and the file that
# recorded them (`cli/src/test_gaps.mo`) is deleted as of Phase 12 -- so
# the record is here: the checker's `resolve_class_method_d4` refuses the
# self-reference and defers, and `lang/src/scope.mo`'s
# `find_concrete_matching_carrier_any` prefers a candidate that pins the
# matched instance's type variables down over one that leaves them
# generic. Order matters and was measured: with only the first half,
# `(some 1) == (List.get ...)` passed while the reverse operand order still
# SIGSEGVed.
# `std/src/qualified_ref_tests.mo` left this list with Phase 3, in
# lockstep with its `check_gap_files` entry (since deleted). A qualified
# reference in
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
# The scratch directory, private to this checkout. One definition, shared with
# bootstrap-compile.sh, debug-oracle.sh and tools/debug_transparency_oracle.sh
# -- see scripts/lib/bootstrap-dir.sh, including why TMPDIR is no longer
# consulted for this path. Private is the point here: `/tmp` is shared by every
# worktree on the machine, and this job's `$out/monad` is the compiler it is
# grading.
# shellcheck disable=SC2034  # read by the sourced helper, not here
MONAD_REPO_ROOT="$root"
# shellcheck source=scripts/lib/bootstrap-dir.sh
# shellcheck disable=SC1091  # the hook runs bare `shellcheck`; the line above names the path for -x
. "$root/scripts/lib/bootstrap-dir.sh"
out="$MONAD_BOOTSTRAP_DIR"
mkdir -p "$out"
# All four motes, not just lang/: cli/ holds the compile target, llvm/ and
# runtime/ the backend. The staleness check and the build command live in
# scripts/build-self-hosted.sh so all three CI scripts share one definition.
# `MONAD_BIN` short-circuits it -- see the header for what CI points it at.
# The directory is made here either way, because the check log below lands
# in it and the build is the only thing that used to create it.
if [ -n "${MONAD_BIN:-}" ]; then
  monad="$MONAD_BIN"
else
  scripts/build-self-hosted.sh "$out" --release
  monad="$out/monad"
fi

# The self-hosted sweep: the whole corpus, with no exclusions at all.
# `host_only` was the last registry and it is deleted above, so the loop
# that read it is gone with it.
#
# `bench` is now swept here as well as checked below. It was the one
# directory the check `find` covered and this one did not, and that gap
# was not cosmetic: `bench/src/hashmap_bucket_dispatch.mo` had been
# failing to compile on an unwired `number::U64.add` native for as long
# as the file has existed, and nothing reported it, because `check`
# cannot see an unwired native -- only codegen can. Adding it here found
# it on the first run, which is why the two `find` lists now agree.
# SHARDING. Both corpus phases below gave their whole target list to ONE
# `monad` process, which walks it a file at a time (`run_test_loop`,
# cli/src/main.mo:836). Measured on the runner (run 36243944155), that is
# 42m23s for the sweep and 8m44s for the check, out of a 51m20s step --
# the sweep alone is most of the job that runs it. They are sharded here:
# MONAD_SWEEP_JOBS processes, one shard each, running concurrently.
#
# Safe by construction, because of what the two commands write and
# nothing else: `monad test` puts every artifact under
# `/tmp/monad_out_<pid>/` (`monad_test_bin_<n>` / `monad_test_result_<n>`
# inside it) and `monad check` writes only the redirect at the call site.
# Neither has a fixed name, so N processes never share one -- and the
# corpus is read only.
#
# That path is HARDCODED `/tmp`, not `${TMPDIR:-/tmp}`: `default_output_dir`
# is `Path.path ("/tmp/monad_out_" ++ I64.to_string process_id)`
# (cli/src/main.mo:33) and reads no environment at all. The pid is the whole
# of what makes the shards safe, so setting TMPDIR does NOT make their
# writes private -- the script's own directories do honour TMPDIR
# (bootstrap-compile.sh:44,141), the compiler's do not.
#
# The split is by BYTES, not by file count. A target's cost is dominated
# by the target: its dependency closure is re-emitted for it, so the
# closure is roughly a constant added to that file's own work, and the
# corpus spans four orders of magnitude (`lang/src/module.mo` is ~200 KB).
# A count-balanced split puts that one file in a shard of 25 -- a quarter
# of the corpus by bytes -- and the wall clock is then that one shard.
# Greedy biggest-first is the standard 4/3-of-optimal assignment and needs
# no cost model to stay honest.
#
# MONAD_SWEEP_JOBS=1 is exactly the single invocation this job used to
# make: same argv, same transcript. That is what lets the serial and the
# sharded totals be compared by running this one script twice.
#
# What parallelism does NOT buy, written down because the honest number is
# what this is judged on: each shard process loads its own program closure
# before it can touch a file, and the `ModuleInfoCache` that serves most
# dependency loads from an earlier file's work within a run is
# per-process (`run_test_loop`'s own doc comment). So N shards pay N
# warm-ups, and the wall clock is `(T - warmup)/N + warmup`, not `T/N` --
# the warm-up is paid once per shard, not divided by N. (Spelled out
# because the earlier form of this line, `(T - N*warmup)/N + warmup`, is
# algebraically just `T/N`, i.e. the claim it was making.)
#
# THAT WARM-UP HAS NOW BEEN MEASURED, and it is small enough that the model
# above is not what decides the shard count. A fresh process on `monad test
# motes/demo/src/helper.mo` -- a file with no tests in it -- takes 13 s from a
# cold store, and that file plus a second one in the SAME process takes the
# same 13 s, so the per-process term is ~13 s and one small file's own work is
# inside the noise. (The first of the two read 31 s, a cold page cache, which
# is why it is measured twice.) Against a 3849 s shard sum, a 13 s term per
# shard cannot be what this wall is made of: the sweep is WORK-bound.
#
# So the shard count is decided by CORES, and the scaling was measured rather
# than derived -- 2026-10-02, `taskset -c 0-3` (the 4-core runner's shape), the
# compiler already built, the store wiped between runs because CI's `git
# clean -ffdx` starts every job cold, same 231-file corpus:
#
#   4 shards   973s 1233s 715s 928s                        max 1233s  sum 3849s
#   8 shards   786s 1283s 871s 771s 667s 765s 855s 992s     max 1283s  sum 6990s
#   12 shards  38s 1160s 468s 668s 804s 1022s 511s 1036s
#              871s 802s 730s 906s                           max 1160s  sum 9016s
#
# `max` is the phase's wall and it is FLAT -- 1233 / 1283 / 1160 s, a 124 s
# band -- while the summed per-shard wall grows 3849 -> 6990 -> 9016 s. That
# growth IS the answer: each shard's number is wall clock, so it absorbs
# contention, and it nearly triples because 8 or 12 processes sharing 4 cores
# each run proportionally slower. Past `nproc`, more shards buy no shorter
# critical path, only more co-tenancy: the floor is the 3849 s of work over 4
# cores (~962 s) and all three configurations land near 1200 s, so what is
# left over is the machine and its co-tenants rather than the split. (Round
# 1's 58m45s-serial-to-25m35s-at-7-shards reading is not evidence about
# warm-up for the same reason: 7 shards on 4 cores is oversubscribed.)
#
# The default is min(nproc, 8): one shard per core, nothing held back. What
# each extra shard costs is a closure resident in memory rather than a file on
# disk, and that cost was measured rather than assumed on 2026-09-27 -- `monad
# test lang/src/scope.mo`, the heaviest file in this corpus, peaks at 172 MB of
# summed tree RSS -- so memory is not what bounds this and cores are. The
# measurement above is also what a shard count PAST the core count costs: at 8
# and at 12 shards on 4 cores the phase's wall did not improve, and 8 was the
# slowest of the three.
#
# It used to be min(nproc - 1, 8), holding a core back "for the machine". The
# reason to reverse that needs no timing at all: the phase's wall is the
# LARGEST of the shards, so a shard count below the core count can only make
# that maximum longer or leave it equal, never shorter -- the reserved core
# runs nothing while the sweep's critical path is decided on the others. What
# a higher count costs is memory and co-tenant contention, which is measured
# above and does not bind here. (Round 2 argued this from run 36323615273's
# `947s 1425s 1425s` and a 3797 s sum; those per-shard numbers were an
# instrumentation artifact -- see `run_shards` -- so the argument is stated
# from the structure instead, which is where it should have started.)
#
# `nproc` here is the CPU count available to THIS process, which is the whole
# reason CI's two runners disagree: nixos-server (4 cores) reports 4 and
# anders-desktop (8 cores) reports 8, so run 36301331844's 3 shards and run
# 36322856497's 7 were both this line, read correctly, on different hardware.
# CI sets MONAD_SWEEP_JOBS explicitly from scripts/ci-cpu-budget.sh, so this
# default now serves local runs -- which ask the same question the runners do.
sweep_jobs="${MONAD_SWEEP_JOBS:-}"
case "$sweep_jobs" in
  '')
    sweep_jobs="$(nproc 2>/dev/null || echo 1)"
    if [ "$sweep_jobs" -gt 8 ]; then sweep_jobs=8; fi
    ;;
  *[!0-9]*)
    echo "MONAD_SWEEP_JOBS must be a positive integer, got '${sweep_jobs}'" >&2
    exit 2
    ;;
esac
if [ "$sweep_jobs" -lt 1 ]; then
  echo "MONAD_SWEEP_JOBS must be at least 1, got '${sweep_jobs}'" >&2
  exit 2
fi

# One definition for both phases. They are the same corpus, and "the two
# `find` lists agree exactly" was a comment that a later edit could
# falsify silently; a list built once cannot drift from itself. Biggest
# first, which is the order `shard_files` wants.
corpus_dirs=(init std examples lang cli llvm runtime build motes slow_tests bench proofs)
corpus_sizes() {
  find "${corpus_dirs[@]}" -name '*.mo' -printf '%s\t%p\n' | sort -rn
}

# Greedy biggest-first assignment of the `size<TAB>path` lines on stdin
# over $sweep_jobs shards, each written to `$dir/shard-<i>.list`. Echoes
# the number of files it saw, so a caller can tell a corpus that came out
# empty from one that was never read.
shard_files() {
  local dir="$1"
  local -a load paths
  local i size path heaviest seen=0
  for ((i = 0; i < sweep_jobs; i++)); do
    load[i]=0
    paths[i]=""
  done
  while IFS=$'\t' read -r size path; do
    [ -n "$path" ] || continue
    heaviest=0
    for ((i = 1; i < sweep_jobs; i++)); do
      if [ "${load[i]}" -lt "${load[heaviest]}" ]; then heaviest="$i"; fi
    done
    paths[heaviest]="${paths[heaviest]}${path}"$'\n'
    load[heaviest]=$((load[heaviest] + size))
    seen=$((seen + 1))
  done
  for ((i = 0; i < sweep_jobs; i++)); do
    printf '%s' "${paths[i]}" > "$dir/shard-${i}.list"
  done
  echo "$seen"
}

# Run `monad <subcmd>` once per non-empty shard, concurrently, each to its
# own `$dir/<subcmd>-<i>.log`; then concatenate them in shard order into
# `$dir/<subcmd>.log`. Sets four arrays the callers read back: `shard_rcs`
# (each shard's exit status, "" for a shard that was never launched),
# `shard_files_n` (how many files it was handed), `shard_pids`, and
# `shard_secs` -- each shard's OWN wall clock, written by the shard itself
# just before it exits (see the launch below for why it must be the shard and
# not this loop). The phase's wall is the LARGEST of them, never their sum;
# their spread is the imbalance left on the table, and their sum is the work
# the split had to divide.
#
# `shard_wall_summary` is left for the caller to echo, and deliberately not
# echoed here: this function writes the transcript to a file the caller
# `cat`s afterwards, so a line printed here would land in front of 197
# files of per-test output instead of beside the aggregate line that says
# what the phase cost.
#
# Why this exists: round 1 sharded on a hypothesis and recorded no
# per-shard time, so the one post-sharding CI run could only INFER that a
# phase did not scale -- from its job total, 544s at one shard against 552s
# at three. That is a fact about the machine, and the wall-clock formula in
# the header is a fact about the split; neither is visible in a log without
# these numbers, and every future shard-count decision was left
# unreasoned. `MONAD_SWEEP_JOBS=1` prints a single number here, which is
# the serial figure round 1's 2.15x was measured against.
#
# Every launch happens before the first `wait`, or the "concurrency" would
# be a sequence; the `wait`s then block in shard order, which is also what
# makes the concatenated transcript deterministic rather than a race.
run_shards() {
  local dir="$1" subcmd="$2"
  local i f s max min=-1 walls="" total=0
  local -a targets
  shard_rcs=()
  shard_files_n=()
  shard_pids=()
  shard_secs=()
  shard_wall_summary=""
  : > "$dir/${subcmd}.log"
  for ((i = 0; i < sweep_jobs; i++)); do
    shard_rcs[i]=""
    shard_files_n[i]="$(wc -l < "$dir/shard-${i}.list")"
    [ "${shard_files_n[i]}" -gt 0 ] || continue
    # A `while read` loop rather than `mapfile`: this repo's shell is
    # bash, but the same line copied into a zsh context yields an EMPTY
    # array from `mapfile` and silently tests nothing.
    targets=()
    while IFS= read -r f; do targets+=("$f"); done < "$dir/shard-${i}.list"
    # Each shard times ITSELF, in its own subshell, and writes its duration
    # beside its log. Timing it from the `wait` loop below instead is what
    # this used to do and it was wrong: those waits run in shard ORDER, not in
    # finish order, so a shard that finished early is stamped with the finish
    # of whichever lower-indexed shard the loop was still blocked on. The
    # recorded value is therefore a running MAXIMUM -- and because all the
    # shards are launched inside the same integer second, every shard that was
    # overtaken reports an IDENTICAL number. Run 36336502690's `1220s` seven
    # times, and run 36323615273's `1425s 1425s`, are both that artifact;
    # round 2 read them as work and sized a shard-count change on the sum.
    # `SECONDS` keeps its epoch across the fork, so this is the same primitive
    # read on the shard's own clock. `$rc` is carried out and re-exited so the
    # parent's `wait` still sees the COMPILER's status, not the writer's.
    (
      s0=$SECONDS
      rc=0
      "$monad" "$subcmd" "${targets[@]}" > "$dir/${subcmd}-${i}.log" 2>&1 || rc=$?
      printf '%s\n' "$((SECONDS - s0))" > "$dir/${subcmd}-${i}.secs"
      exit "$rc"
    ) &
    shard_pids[i]=$!
  done
  for ((i = 0; i < sweep_jobs; i++)); do
    [ -n "${shard_pids[i]:-}" ] || continue
    shard_rcs[i]=0
    wait "${shard_pids[i]}" || shard_rcs[i]=$?
    # The shard wrote this before exiting, so it exists once `wait` returns.
    # `|| true` because `set -e` would otherwise abort on a missing file, and
    # an absent reading is skipped by the summary loop below. An absent one
    # means the shard died before it could write -- an OOM kill is the case
    # that matters -- which leaves `rc` non-zero and the run red, so a `max`
    # that understates the wall there cannot flatter a green run.
    shard_secs[i]="$(cat "$dir/${subcmd}-${i}.secs" 2>/dev/null || true)"
    cat "$dir/${subcmd}-${i}.log" >> "$dir/${subcmd}.log"
  done
  max=0
  for ((i = 0; i < sweep_jobs; i++)); do
    [ -n "${shard_secs[i]:-}" ] || continue
    s="${shard_secs[i]}"
    walls="${walls}${walls:+ }${s}s"
    if [ "$s" -gt "$max" ]; then max="$s"; fi
    if [ "$min" -lt 0 ] || [ "$s" -lt "$min" ]; then min="$s"; fi
    total=$((total + s))
  done
  if [ -n "$walls" ]; then
    shard_wall_summary="shard walls ${walls} -- max ${max}s is this phase's wall, spread $((max - min))s, sum ${total}s of work"
  fi
}

# One shard's verdict, from its log and status. A non-zero status is a
# failure unless the shard had nothing runnable in it: `No tests found` is
# what a whole invocation prints when it ends with
# `tests_passed + tests_failed == 0` (cli/src/main.mo:839-845), which is
# the truth for a shard of files with no `#[test]`s -- and ALSO for a shard
# whose every file failed to compile, since a file whose driver was never
# produced moves neither counter. The `file(s) skipped` line separates
# them: it is printed only for files that had no runnable tests, so a
# shard whose skips account for every file it was handed really did have
# nothing to run, and anything else is a failure. Without this, one shard
# of compile failures would exit 1 like a shard of no-tests files, and the
# aggregate total would still be non-zero -- a false green of exactly the
# kind this script's own `set -e` bug was.
#
# The `skipped == given` rescue is believed UNREACHABLE, and is kept only as
# a net. A shard exits non-zero iff `tests_failed > 0 || files_failed > 0`
# (cli/src/main.mo:865), and a file that fails a gate or a driver compile
# moves `files_failed` and never `skipped` (:890,904 vs :933,969) -- one
# bucket per file. So `rc != 0` implies at least one file was neither
# skipped nor successful, i.e. `skipped < given`, and the arm cannot fire.
# Driven with four synthetic logs (2026-09-27): all-no-tests rc=1 skipped
# 3/3 -> ok (the arm, reachable only in the fixture); one gate failure
# skipped 2/3 -> failed; a red shard with no `No tests found` -> failed;
# rc=0 -> ok. The distinction that actually catches compile failures is the
# `No tests found` grep above plus the comparison, not a rescue of them.
shard_verdict() {
  local log="$1" given="$2" rc="$3"
  local skipped
  if [ "$rc" -eq 0 ]; then echo ok; return; fi
  if ! grep -q '^No tests found$' "$log"; then echo failed; return; fi
  skipped="$(sed -e 's/\x1b\[[0-9;]*m//g' "$log" \
    | awk -F'[/ ]' '/^[0-9]+ file\(s\) skipped/ { s += $1 } END { printf "%d", s + 0 }')"
  if [ "$skipped" = "$given" ]; then echo ok; else echo failed; fi
}

# Per-run, so two runs sharing a TMPDIR (the default one is shared by every
# worktree and runner on this machine) cannot read each other's shard lists
# or logs -- the same hazard the shard targets themselves avoid by being
# pid-unique.
shard_dir="$out/shards-$$"
mkdir -p "$shard_dir"
corpus_files="$(corpus_sizes | shard_files "$shard_dir")"
if [ "$corpus_files" -eq 0 ]; then
  echo "self-hosted sweep: the corpus is empty (${corpus_dirs[*]} hold no .mo files) -- check the find above against the tree" >&2
  exit 1
fi

self_hosted_rc=0
run_shards "$shard_dir" test
for ((i = 0; i < sweep_jobs; i++)); do
  [ -n "${shard_rcs[i]}" ] || continue
  if [ "$(shard_verdict "$shard_dir/test-${i}.log" "${shard_files_n[i]}" "${shard_rcs[i]}")" != ok ]; then
    # Names the shard, its status and its size before the transcript below
    # repeats them: without this a red run says only that the sweep failed,
    # and the shard a reader needs is the one whose log is a 60-file wall.
    echo "self-hosted sweep: shard ${i} failed -- exit ${shard_rcs[i]}, ${shard_files_n[i]} file(s), its transcript is below" >&2
    self_hosted_rc=1
  fi
done
cat "$shard_dir/test.log"
if [ -n "$shard_wall_summary" ]; then
  echo "self-hosted sweep: ${shard_wall_summary}"
fi

# One aggregate line, summed from the shards' own totals rather than
# re-derived, so the number a reader compares against a serial run is the
# compiler's. `MONAD_SWEEP_JOBS=1` prints it over a single shard, which is
# the same run it was before plus this line.
read -r sweep_passed sweep_total sweep_skipped <<< "$(sed -e 's/\x1b\[[0-9;]*m//g' "$shard_dir/test.log" \
  | awk -F'[/ ]' '
      /^[0-9]+\/[0-9]+ total tests passed$/ { p += $1; t += $2; next }
      /^[0-9]+ file\(s\) skipped/           { s += $1 }
      END { printf "%d %d %d", p + 0, t + 0, s + 0 }')"
echo "self-hosted sweep: ${sweep_passed}/${sweep_total} total tests passed, ${sweep_skipped} file(s) skipped (no tests) -- over ${corpus_files} file(s) in ${sweep_jobs} shard(s)"
if [ "$sweep_total" -eq 0 ]; then
  # A sweep over this corpus cannot legitimately run zero tests: the
  # invocation is broken, not passing. `shard_verdict` above already fails
  # a shard in that state; this catches the same thing stated once for the
  # whole run, which is the number a reader sees.
  echo "self-hosted sweep: NO tests ran at all -- a sweep that finds nothing is a broken invocation, not a pass" >&2
  self_hosted_rc=1
fi
if [ "$self_hosted_rc" -ne 0 ]; then
  # Deliberately NOT fatal: `set -e` used to abort here, which dropped
  # everything after it (the check phase, and before Phase 12 the Rust
  # fallback) whenever a single test failed -- so a red sweep reported one
  # total and nothing else, indistinguishable from a truncated run. The
  # status is re-raised at the end of the script.
  echo "self-hosted tests FAILED -- continuing to the external-mote gate so one red run reports everything it can"
fi

# A COUNT, not a gate. The gate is `shard_rcs` plus `shard_verdict` above,
# which also fails a shard that died without printing anything; this exists
# so the failure is stated as a number beside the totals rather than only as
# per-file lines inside a 197-file transcript.
#
# ANSI-stripped first, and that is not cosmetic: the sweep's FAIL lines are
# colourised (`ESC[31mFAIL  `, cli/src/main.mo:889,903), so a bare
# `grep -cE '^FAIL '` over this log returns 0. The count the deleted check
# phase used to print worked only because `run_check_loop`'s own line
# (cli/src/main.mo:565) is uncoloured -- a difference between the two phases
# that this count has to correct for rather than inherit.
read -r sweep_fails <<< "$(sed -e 's/\x1b\[[0-9;]*m//g' "$shard_dir/test.log" \
  | grep -cE '^FAIL ' || true)"
if [ -z "$sweep_fails" ]; then
  # `grep -c` prints a count or nothing at all: nothing means the log could
  # not be read. Counting that as 0 failures is the "a failed phase is
  # indistinguishable from a passing one" class this script's own `set -e`
  # bug belonged to, so it is stated and it is red.
  echo "self-hosted sweep: could not count FAIL lines in ${shard_dir}/test.log -- that is a broken run, not a clean one" >&2
  sweep_fails=0
  self_hosted_rc=1
fi
if [ "$sweep_fails" != 0 ]; then
  echo "self-hosted sweep: ${sweep_fails} file(s) reported FAIL -- the lines above say which" >&2
  self_hosted_rc=1
fi

# Per-mote affine gate (Phase 6 of the affine-by-default experiment):
# `--affine` promotes a mote's M2 diagnostics (copy_required /
# value_used_after_move / linear_unused) from advisory to hard errors, so a
# mote joins this list only once its violation count has reached zero --
# measured, not guessed, via the bench/src/affine_report.mo corpus sweep and
# the per-file probe in bench/src/affine_probe.mo. `monad check --affine`
# disables the check cache (an affine result must never be replayed as an
# ordinary one and vice versa -- cli/src/main.mo:1106), so each entry here is
# a full elaboration of that mote's files; keep the list to motes that are
# cheap for that reason. A mote with a nonzero count stays warn-only, which
# here means absent: nothing outside this list runs with --affine.
# Like the sweep above, a red gate folds into `self_hosted_rc` rather than
# aborting -- one red run reports everything it can -- and the offending
# mote's own diagnostics are printed so the failure names its binders.
affine_promoted_motes=(proofs runtime)
for m in "${affine_promoted_motes[@]}"; do
  affine_log="$shard_dir/affine-$m.log"
  if "$monad" check --affine "$m" > "$affine_log" 2>&1; then
    echo "affine gate: $m -- 0 violations"
  else
    echo "affine gate: $m FAILED -- M2 diagnostics are hard errors for this mote:" >&2
    cat "$affine_log" >&2
    self_hosted_rc=1
  fi
done

# The corpus-wide self-hosted `check` phase used to run HERE, over the same
# shard lists the sweep above uses, and it was deleted because it was the
# sweep's own per-file gate repeated call for call:
#
#   * `monad test` elaborates and typechecks every file BEFORE emitting code
#     for it -- `elaborate_loaded_modules_cached` (cli/src/main.mo:878) then
#     `check_module_with_scope` (:895) -- and a load failure or any
#     diagnostic is a `FAIL` plus `files_failed + 1` (:889-890, :903-904).
#     It runs before codegen for EVERY file, `#[test]`s or not: the gate sits
#     inside `run_test_loop`, whose elaboration is at :878, and the
#     `run_test_loop_codegen` call it decides against is at :906.
#   * `check_file_cached` (lang/src/module.mo:2203-2212) makes those same two
#     calls with the same arguments, `check_deps=false` included, over the
#     same paths: `expand_check_paths` is identity on files (:2294-2303) and
#     `resolve_target_paths` is subcommand-agnostic (cli/src/main.mo:647-652),
#     so both phases read the SAME `shard-<i>.list`.
#   * The gate is FATAL: `run_test_paths` returns what `run_test_loop`
#     computed, i.e. 1 iff `tests_failed > 0 || files_failed > 0`
#     (cli/src/main.mo:865) -- so a file
#     the old check phase would have FAILed cannot reach codegen and cannot
#     leave the sweep green.
#
# Measured (run 36301331844, when this job was still called `test`): the phase
# cost 552 s of its 3252 s
# -- the second-largest step in the pipeline -- while buying only the
# ok/FAIL matrix the sweep already prints. It also did not scale with
# processes, 544 s at one shard against 552 s at three, which is what says
# its cost was cache-threaded elaboration rather than per-core work; that is
# why deleting it is worth more than sharding it harder.
#
# The old comment here claimed "the pre-commit hook's `monad check` is the
# RUST host -- a different implementation -- so neither gate covers the
# other". That is stale: the self-hosted checker runs per corpus file INSIDE
# the sweep, which is the whole of what this phase was for. Its `bench`
# example argues the other direction and is kept, because it is the argument
# against deleting the SWEEP instead: `bench/src/hashmap_bucket_dispatch.mo`
# passed `monad check` for as long as the file existed while its codegen
# could not compile it at all -- an unwired native is not a check error, so
# only the sweep can see one.
#
# What replaces its SIGNAL, not its work: the per-shard status plus
# `shard_verdict` above (the gate, and strictly stronger than a `FAIL` grep,
# since a shard that died without printing anything still fails it), and the
# ANSI-stripped `FAIL` count printed with the aggregate line below.
#
# Gone with the phase: the `gap_files` registry, whose last entry closed with
# Phase 3, and the per-file history that filled the comment above
# (`std/src/qualified_ref_tests.mo`, `examples/structs.mo`, `lang/src/json.mo`,
# `std/src/concurrent/combine_test.mo`, the `#[derive]` trio). Those files
# report 0 errors and the registry is deleted; the record of each cause and
# fix belongs to this script's git history, not to a live exception list.

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

# The external-mote end-to-end check last, because it is the one thing here
# that does not run over the corpus: it builds a mote in a temp directory
# OUTSIDE the checkout and runs this same binary from inside it, in every
# configuration an external repository can be in -- seven, see its header.
# Nothing else in the repo ever ran the CLI from a foreign working directory,
# which is how a whole class of resolution gaps survived a green suite; see
# the script's header.
#
# Placed before the status is re-raised so a failure here fails the sweep,
# and given `$monad` rather than a path of its own -- a second binary would be
# a second thing that can be stale. `$monad` is the one this job is testing:
# under CI's `MONAD_BIN` it is the flake's compiler, and `$out/monad` would be
# a path this job never wrote (`scripts/bootstrap-compile.sh` builds exactly
# that path, in the same checkout) -- i.e. the gate would grade another job's
# binary, or whatever an earlier run left behind, or fail outright because
# nothing is there. The bootstrap directory being per-checkout is what makes
# that argument true: it was `/tmp/monad-bootstrap-ci` when this was written,
# shared by every worktree on the machine.
"$(dirname -- "$0")/check-external-mote.sh" "$monad"

# Re-raise the captured self-hosted status: without this the `|| self_hosted_rc=$?`
# above would turn a red run into an exit 0, which is worse than the abort it
# replaced. Nothing between the sweep and here can exit 1 on the sweep's
# behalf any more -- the check phase that used to do that is deleted -- so
# this is now the ONLY place a red sweep becomes a red script.
exit "$self_hosted_rc"
