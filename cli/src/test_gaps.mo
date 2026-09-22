/// Known test-runner gaps: files whose test driver cannot be built
/// today, for a reason already understood and recorded here.
///
/// **This file is scaffolding and is expected to reach zero entries and
/// be deleted.** Every entry names the condition that removes it. It
/// exists so that `monad test` can FAIL on an unknown failure (the
/// default) while still not failing CI on the known, tracked ones --
/// before this, every file the runner could not build was silently
/// counted as `skipped`, which affects no exit code, so those tests ran
/// nowhere at all and nothing said so.
///
/// The 2 entries here are what a full corpus sweep actually reports,
/// not a guess, and neither is a problem with the test files themselves.
/// Both are the same thing: the async runtime, which does not exist --
/// `std/src/concurrent/fiber_test.mo` (the unwired `fork_io`/`await_fiber`
/// family) and `std/src/concurrent/combine_test.mo` (the same family's
/// `scope_new`/`scope_drop`/`scope_fork`/`sleep_io`; this is ALL that is
/// left of that file -- its checker failure is CLOSED, see the Phase-1
/// paragraph below).
///
/// Each closed gap is recorded here rather than deleted outright, so the
/// next reader can tell a fix from a re-registration.
///
/// PHASE 1 IS CLOSED, and these three were its whole registry footprint:
/// `lang/src/json.mo` (56/56), `examples/indexed_monads.mo` (3/3) and
/// `examples/state_monad.mo` (5/5) all run self-hosted now, and
/// `std/src/concurrent/combine_test.mo` has stopped failing its checker
/// (it reaches the natives above instead, which is why it stays listed).
/// Measured with a binary rebuilt from the fix. The channel they were
/// waiting on was one missing thing in two places, both in
/// `lang/src/scope.mo`'s carrier inference:
///
///   1. an application whose HEAD is a local variable -- a def's own
///      parameter, or a `let`-bound name -- produced NO carrier at all
///      (`infer_carrier_type`'s `Term.app` arm knew only `def_types` and
///      `ctor_owners`), so `Monad.bind (f s) ...` inside
///      `combine.mo`'s `scoped (f : Scope -> IO A)` had nothing to infer
///      `IO` from. The other two binds in that same def are named defs
///      (`scope_new`, `scope_drop s`) and always had a carrier, which is
///      why only that one shape failed, and why the do-block spelling and
///      the hand-written nest failed IDENTICALLY -- the desugaring was
///      never involved;
///   2. a def call whose own declared return type has no type variable to
///      instantiate (`get_obj : I64 -> IO Obj`) reported the BARE head
///      (`IO`), which binds nothing against a parameter shape like `M A`
///      -- so the callee-signature hint channel dropped the whole
///      parameter hint and every class call inside the enclosing lambda
///      stayed unresolved.
///
/// Both now keep the return type APPLIED (`IO Obj`), which is what
/// `bind_term_vars` needs to bind `M := IO`.
///
/// `#[derive]`/`#[derive_cli]` is CLOSED, and with it the whole
/// attribute/decl-gen family: `std/src/derive_tests.mo` (22/22),
/// `cli/src/tests/cli_derive_tests.mo` (7/7) and `examples/derive.mo`
/// (7/7) all run self-hosted now. Three things were missing, in the
/// order they were hit: the parser refused an attribute on a `struct`
/// decl at all (so `examples/derive.mo` stopped dead AT the attribute,
/// which is why its recorded cause read "Failed to load" -- a load
/// failure, not the codegen one underneath); nothing bridged an
/// attribute to the decl-gen macros that exist on the host (so
/// `#[derive_cli]` expanded to nothing and every body referenced an
/// unknown variable); and a value-position reference to a struct's
/// implicit constructor -- `Point.mk`, the shape `e_ctor` reifies to
/// (`std/derive.mo`'s `lens_setter`) -- was not recognized as a
/// constructor, so it compiled to a call to a function that is never
/// defined (`llc: use of undefined value '@Point.mk'`). That last one
/// needed BOTH halves: the constructor-arity table has to know a
/// struct's `mk` (`extract_structs`), and the decl list codegen is
/// handed has to still CONTAIN the struct (`filter_reachable_decls`),
/// which keeps them for the same reason it keeps inductives.
///
/// The macro-DERIVED-instance failure this file used to record -- a
/// generated `BEq Point` reported as "no instance found for `BEq.beq`"
/// while a hand-written `instance BEq Point` passed -- is CLOSED by the
/// same bridge, not by the carrier work: the derived instance is a real
/// instance once the attribute actually expands.
///
/// FLOATING POINT is CLOSED, and with it the whole native-wiring family:
/// `i64_to_u64`/`u8_to_u64` are identity conversions and the U16/I8
/// comparison families are unmasked `icmp`, both matching the Rust
/// reference's own semantics, and the F64 family (`f64_add`/`sub`/`mul`/
/// `div`/`eq`/`lt`/`gt`/`to_string`, plus the `f64_of_string` the
/// compiler itself calls to lower a float literal into its bit pattern)
/// is wired in `runtime/src/runtime.c` and `lang/src/codegen/natives.mo`.
/// That is what took `std/src/map_tests.mo`, `std/src/test_map_full.mo`,
/// `init/src/optics_tests.mo`, `examples/optics.mo` and `std/src/base.mo`
/// off this list -- three of them on the strength of a native that was
/// missing, two on the strength of a FEATURE that was.
///
/// Two independent bugs surfaced while closing it, both recorded where
/// they live rather than here: a chained un-annotated `let m2 :=
/// Map.insert ... m1` took its carrier from `Map`'s DEFAULT instead of
/// from `m1`'s own `BTreeMap` (`lang/src/scope.mo`'s `let_binder_type`),
/// and a float literal's text was REBUILT from the parser's `I64`
/// accumulator, which wraps past `i64::MAX`, so
/// `100000000000000000000.0` compiled to a different double
/// (`lang/src/parser/number.mo`'s `numeric_literal_try_dot` now slices
/// the source text instead).
///
/// The legacy dotted-path family (~105 call sites across 8 files) that
/// used to head this list is CLOSED: the call sites now import the bare
/// name they call, and both parsers reject a dotted `use` path outright.
/// The other codegen family that used to sit here -- the generic `Add`
/// dict self-recursion on an untyped lambda's accumulator
/// (`init/src/foldable_tests.mo`, `init/src/foldable_tests_fold.mo`) -- is
/// CLOSED too; both files are 14/14 and 10/10 self-hosted.
///
/// The dictionary self-reference family that used to sit here
/// (`init/src/tests.mo`, the last entry this list had for a DEAD DRIVER)
/// is CLOSED: 102/102 self-hosted. Its minimal repro was
///
///     #[test]
///     def p_get_0 : Bool := some 1 == (List.get 0 [1, 2, 3])
///
/// and it failed at BOTH operand orders, not only the one it was
/// recorded with. `List.get 0 [1, 2, 3]` reports a still-GENERIC carrier
/// (`Option A`), which matches the very option instance being expanded
/// and leaves its own `[BEq A]` constraint bound to nothing, so the
/// element slot of the emitted comparison received the option instance's
/// own dictionary. Fixed in two halves, one per resolver, and both are
/// needed: the checker refuses such a self-reference and DEFERS
/// (`lang/typecheck/infer.mo`'s `dict_args_contain_self` -- it has no
/// argument carriers of its own to fall back on), and `lang/scope.mo`'s
/// `find_concrete_matching_carrier_any` then prefers a candidate that
/// pins the matched instance's type variables down over one that leaves
/// them generic (the codegen pass never sees a call the checker already
/// rewrote, so it cannot be the only place this is fixed).
///
/// A DEF'S OWN NAMED-CALL DEFAULTS is CLOSED (`examples/structs.mo`,
/// 10/10 self-hosted), the last entry this file has held for a checker
/// error rather than an unwired runtime. It was a missing CHANNEL,
/// exactly as recorded: `ScopeData.def_params` was a `List (Pair
/// Identifier Term)` because it was recovered from the def's own
/// `Term.lam` chain, and `Term.lam` has no default slot -- so
/// `def scale {factor : I64 := 2, p : I64}` reached the checker with
/// `factor`'s default gone. `Def` and `ParseDef` now carry the DECLARED
/// parameter list (`List Param`, threaded from the parser's brace-form
/// block through `lower_parse_def`), so a named call on a def and one on
/// a constructor are validated by the same helpers, and a default stands
/// in for an omitted field on both. Every `ParseDef`/`Def` match site was
/// converted to a named-field pattern in the same change, which is what
/// makes this the last field either struct can gain at that price.
///
/// CROSS-MODULE QUALIFIED REFERENCES is CLOSED
/// (`std/src/qualified_ref_tests.mo`, 4/4 self-hosted). Its recorded
/// cause was right about the shape -- the flatten drops each decl's
/// owning module -- and the recorded fix was the wrong half: routing the
/// pipeline through `build_scope_from_modules` is unusable as written,
/// because `build_scope_from_one_module` registers defs, inductives,
/// instances and infixes and NONE of the classes or of the
/// `def_params`/`def_sigs` side tables, so it would silently regress the
/// checker -- and it has no production caller at all. The flatten now
/// carries each decl's own owning module instead: `DeclGroup`
/// (`lang/src/types.mo`) pairs a `ModulePath` with that module's decls,
/// and `build_scope_from_groups` (`lang/scope.mo`) folds ONE GROUP AT A
/// TIME so each def registers under its real module. The four
/// whole-graph passes could not simply be applied per module -- the
/// promotion pass collects its class table from its own argument, so a
/// module promoted in isolation would lose every instance whose class is
/// declared elsewhere; they collect globally off the flattened view and
/// append per-owner promotion tail groups, which reproduces the flat
/// result exactly. That was one half. The other half was the pair
/// match's NAME comparison in `find_def_by_module_and_name`: a DECLARED
/// name is built by `dotted_def_name` -> `Identifier.id` ->
/// `NamePath.npath [id]`, so `pub def String.concat` is ONE segment
/// holding an embedded dot, while a reference's name half is
/// `split_ids`-split per dot into TWO -- and `name_path_similar` is
/// element-wise, so a dotted name half could never match. That is
/// exactly why the file's single-segment `std::process::process_id`
/// resolved as soon as the module was right while
/// `init::string::String.concat` did not, and the comparison is on the
/// RENDERED name now, which is the canonical spelling this model keys
/// defs by.
///
/// **Matching is on path AND cause**, deliberately: a listed file that
/// starts failing for a NEW reason is reported as a real failure, not
/// excused by its presence here. The cause is matched as a substring of
/// the driver-compile error, so each token below must be harvested from
/// the real binary's own output, never transcribed from prose.
///
/// Three index-aligned `List String`s rather than a list of structs.
/// That shape was forced: a user struct constructor inside a list
/// literal used to miscompile through the native backend (`TestGap.mk`
/// inside `[...]` emitted a call to an undefined `@TestGap.mk` and `llc`
/// rejected the module), which is the same missing constructor-arity
/// entry the `#[derive]` family above needed. That is FIXED, and the
/// shape is verified to compile now -- but the lists are left as they
/// are rather than churned into a struct list at the tail end of the
/// change that fixed them, and `test_gap_lists_are_aligned` still
/// guards the alignment this shape gives up.

/// Paths, exactly as the runner reports them (repo-relative; identical
/// whether the user passes a directory or explicit files).
pub def gap_paths : List String :=
    ["std/src/concurrent/fiber_test.mo",
     "std/src/concurrent/combine_test.mo"]

/// The distinguishing substring of each file's own known error.
///
/// Harvested from the real binary's own output, and note that the
/// string differs by WHICH stage fails: a driver-compile error carries
/// the compiler's message, while a failure that happens earlier -- or in
/// a dead driver -- is matched against the wording the RUNNER itself
/// prints for it ("compilation failed", "driver exited -1"), because
/// llc's own message goes to the console, not into a value the runner
/// holds. No entry needs either of those two wordings today: A8 was the
/// last one to (`init/src/tests.mo`'s dead driver), and it is closed.
pub def gap_causes : List String :=
    ["native `fork_io`",
     // The unwired-native family, not the checker: the message this token
     // is harvested from lists every native the file needs
     // (`fork_io`, `cancel_fiber`, `await_fiber`, `scope_new`,
     // `scope_drop`, `scope_fork`, `sleep_io`). `scope_fork` is unique to
     // `combine.mo` -- `fiber.mo` declares none of the `scope_*` families
     // -- so the two async entries stay distinguishable.
     "native `scope_fork`"]

/// Why each gap is open, and what closes it.
pub def gap_reasons : List String :=
    // Closed by: a self-hosted async runtime. Tracked in
    // plans/bootstrapping/self-hosted-async-runtime.md.
    ["async runtime not self-hostable yet (fork_io/await_fiber unwired)",
     // The async runtime, which is the ONLY thing left in this file: its
     // checker failure -- the missing expected-type channel that used to
     // report `no instance found for `Monad.bind` (needed in
     // `std.concurrent.combine::scoped`)` -- is CLOSED (see this file's
     // header). It now stops on the unwired natives above, exactly as
     // `fiber_test.mo` does, and both leave this list together when the
     // runtime lands. Its own `scoped (f : Scope -> IO A)` is what
     // isolated the local-variable-head half of that channel, and it is
     // the minimal repro for it: the two other binds in the same def call
     // named defs (`scope_new`, `scope_drop s`) and always had a carrier.
     "async runtime not self-hostable yet (scope_new/scope_drop/scope_fork/sleep_io unwired)"]

#[partial]
def gap_len (xs : List String) : I64 :=
    match xs {
        List.empty => 0,
        List.cons _ rest => 1 + gap_len rest,
    }

/// Index of `path` in `gap_paths`, or -1. Walks the list rather than
/// using a map: the list is short, and it is expected to shrink.
#[partial]
def gap_index_of (paths : List String) (path : String) (i : I64) : I64 :=
    match paths {
        List.empty => 0 - 1,
        List.cons p rest =>
            if String.beq p path then i else gap_index_of rest path (i + 1),
    }

#[partial]
def gap_nth (xs : List String) (i : I64) : String :=
    match xs {
        List.empty => "",
        List.cons x rest => if I64.beq i 0 then x else gap_nth rest (i - 1),
    }

/// Whether `path` is a known gap failing for its own recorded reason.
///
/// Both halves must match: an unknown path is not a gap, and neither is
/// a listed path whose error no longer contains its recorded cause --
/// that is a NEW failure in a file that happens to be listed, and it
/// must be reported.
pub def is_known_gap (path : String) (err : String) : Bool :=
    let i := gap_index_of gap_paths path 0 in
    if I64.lt i 0 then false
    else String.contains err (gap_nth gap_causes i)

/// The recorded reason for a known gap, for the runner's own message.
pub def gap_reason_for (path : String) : String :=
    let i := gap_index_of gap_paths path 0 in
    if I64.lt i 0 then "" else gap_nth gap_reasons i

// ─── Tests ──────────────────────────────────────────────────────────

#[test]
def test_gap_lists_are_aligned : Bool :=
    I64.beq (gap_len gap_paths) (gap_len gap_causes)
    && I64.beq (gap_len gap_paths) (gap_len gap_reasons)

#[test]
def test_is_known_gap_matches_listed_file_with_its_cause : Bool :=
    is_known_gap "std/src/concurrent/fiber_test.mo" "native `fork_io` (needed by def `io::fork_io`) is not wired"

#[test]
def test_is_known_gap_rejects_unknown_cause_on_listed_path : Bool :=
    // The whole point of matching on cause as well as path: this file
    // is listed, but THIS failure is not the one it is listed for.
    Bool.not (is_known_gap "std/src/concurrent/fiber_test.mo" "parse error: unexpected token at 12:3")

#[test]
def test_is_known_gap_rejects_unlisted_path : Bool :=
    Bool.not (is_known_gap "std/src/list.mo" "driver exited -1")

/// The f64 family's three files are off the registry (P9), and this
/// pins that: if a later change makes one of them fail again, that
/// failure must be REPORTED -- a stale entry would be exactly the thing
/// that hides it. `is_known_gap` matches on path first, so a path that
/// is no longer listed cannot be excused by any cause string at all.
#[test]
def test_closed_f64_gaps_are_no_longer_listed : Bool :=
    Bool.not (is_known_gap "init/src/optics_tests.mo" "native `f64_mul`")
    && Bool.not (is_known_gap "examples/optics.mo" "native `f64_eq`")
    && Bool.not (is_known_gap "std/src/base.mo" "native `f64_eq`")

/// Same pin for the `#[derive]` family (P10), and for the same reason:
/// all three of these were listed for a cause that no longer exists, so
/// a future failure in any of them is a NEW failure and has to be
/// reported rather than excused. The cause strings are the ones that
/// used to be recorded for them.
#[test]
def test_closed_derive_gaps_are_no_longer_listed : Bool :=
    Bool.not (is_known_gap "std/src/derive_tests.mo" "no instance found for `BEq.beq`")
    && Bool.not (is_known_gap "cli/src/tests/cli_derive_tests.mo" "does not typecheck")
    && Bool.not (is_known_gap "examples/derive.mo" "Failed to load")

/// Same pin for Phase 1's three files, and for the same reason: each was
/// listed for a cause that no longer exists, so a future failure in any
/// of them is a NEW failure and must be reported rather than excused. The
/// cause strings are the ones that used to be recorded for them (for
/// json.mo and indexed_monads.mo, the checker's own wording; for
/// state_monad.mo, its instance-resolution failure).
#[test]
def test_closed_expected_type_gaps_are_no_longer_listed : Bool :=
    Bool.not (is_known_gap "lang/src/json.mo" "expected A, found Bool")
    && Bool.not (is_known_gap "examples/indexed_monads.mo" "no instance found for `Monad.pure`")
    && Bool.not (is_known_gap "examples/state_monad.mo" "no instance found for `MonadState.modify_get`")

/// Same pin for A8, the dictionary self-reference: the only entry this
/// list ever had for a DEAD DRIVER, and the file behind BOTH of the
/// runner's non-compiler wordings -- its earlier `@Pred` link failure is
/// why the "compilation failed" branch tests for a gap at all, and its
/// dead driver is what "driver exited -1" was recorded for. Both branches
/// stay where they are with no entry left to exercise them, because which
/// stage fails is a property of a gap, not something its author chooses.
/// The cause strings are the ones that used to be recorded for it.
#[test]
def test_closed_driver_signal_gap_is_no_longer_listed : Bool :=
    Bool.not (is_known_gap "init/src/tests.mo" "driver exited -1")
    && Bool.not (is_known_gap "init/src/tests.mo" "compilation failed")

/// Same pin for A7, cross-module qualified references (Phase 3), and
/// for the same reason: it was listed for a cause that no longer exists,
/// so a future failure in it is a NEW failure and must be reported
/// rather than excused. The cause string is the one that used to be
/// recorded for it.
#[test]
def test_closed_qualified_ref_gap_is_no_longer_listed : Bool :=
    Bool.not (is_known_gap "std/src/qualified_ref_tests.mo" "does not typecheck")

/// `combine_test.mo` is STILL listed, but for the async reason now rather
/// than the checker one, and this pins both halves: its recorded cause
/// has to be a token that really occurs in the natives message (or the
/// entry would excuse nothing and the file would be reported FAIL), and
/// it must no longer be excusing the `Monad.bind` failure that Phase 1
/// closed -- a file left listed for a cause it no longer fails for is
/// exactly what hides a regression.
#[test]
def test_combine_test_is_listed_for_the_native_family_only : Bool :=
    is_known_gap "std/src/concurrent/combine_test.mo" "native `scope_fork` (needed by def `std.concurrent.combine::scope_fork`) is not wired"
    && Bool.not (is_known_gap "std/src/concurrent/combine_test.mo" "no instance found for `Monad.bind`")

#[test]
def test_gap_reason_for_listed_path : Bool :=
    String.contains (gap_reason_for "std/src/concurrent/fiber_test.mo") "async runtime"

#[test]
def test_gap_reason_for_unlisted_path_is_empty : Bool :=
    String.beq (gap_reason_for "std/src/list.mo") ""
