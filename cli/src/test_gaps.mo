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
/// The 7 entries here are what a full corpus sweep actually reports,
/// not a guess, and none is a problem with the test files themselves. In
/// rough order of how much they cost to close:
///
///   * self-hosted checker gaps -- instance resolution with no carrier-
///     revealing argument to infer one from (`Monad.pure`,
///     `MonadState.modify_get`), the expected-type channel the parser's
///     discarded ascriptions leave empty (`combine_test.mo`, `json.mo`),
///     and a named call's own declared defaults, which do not survive the
///     parser (`structs.mo`) -- 5 files;
///   * a codegen bug the checker used to hide (`init/src/tests.mo`) --
///     1 file;
///   * the async runtime, which does not exist (1 file).
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
/// `init/src/tests.mo` is a PRE-EXISTING failure, not fallout from any
/// change listed above: the same 4-line repro fails identically on a
/// self-hosted binary built at afa2f92 (the commit before this branch's
/// own .mo work began), and passes on the Rust evaluator -- measure with
/// the self-hosted binary, because `monad-rs test` runs the Rust
/// implementation and never touches this compiler at all.
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
     "init/src/tests.mo",
     "std/src/concurrent/combine_test.mo",
     "lang/src/json.mo",
     "examples/structs.mo",
     "examples/indexed_monads.mo",
     "examples/state_monad.mo",
     "std/src/qualified_ref_tests.mo"]

/// The distinguishing substring of each file's own known error.
///
/// Harvested from the real binary's own output, and note that the
/// string differs by WHICH stage fails: a driver-compile error carries
/// the compiler's message, while a link failure and a dead driver are
/// matched against the wording the runner itself prints for them
/// ("compilation failed", "driver exited -1") because llc's own
/// message goes to the console, not into a value the runner holds.
pub def gap_causes : List String :=
    ["native `fork_io`",
     "driver exited -1",
     "does not typecheck",
     "does not typecheck",
     "does not typecheck",
     "no instance found for `Monad.pure`",
     "no instance found for `MonadState.modify_get`",
     "does not typecheck"]

/// Why each gap is open, and what closes it.
pub def gap_reasons : List String :=
    // Closed by: a self-hosted async runtime. Tracked in
    // plans/bootstrapping/self-hosted-async-runtime.md.
    ["async runtime not self-hostable yet (fork_io/await_fiber unwired)",
     // NOT the `Pred` gap any more -- that one is CLOSED (codegen emits a
     // boxed constant for the four builtin sort names, so `get_sort Pred`
     // no longer reaches llc as an undefined `@Pred`), and the failure
     // moved from the link to a dead driver. What is left is a
     // dictionary-argument self-reference, and it is PRE-EXISTING: the
     // same 4-line repro fails on a self-hosted binary built at afa2f92,
     // and passes on the Rust evaluator (which is a different
     // implementation -- `monad-rs test` never runs this compiler).
     //
     // Minimal repro, measured against the self-hosted binary:
     //
     //     #[test]
     //     def p_get_0 : Bool := some 1 == (List.get 0 [1, 2, 3])
     //
     // `init/src/tests.mo:105` is that shape (`test_get_0`). The
     // element-dict slot of the emitted comparison holds the option
     // instance's OWN dictionary instead of the element's:
     //
     //     %t167 = call @"init::__Dict_BEq_Option_A"()
     //     ...
     //     %t175 = call @"init::BEq_Option_A_beq"(%t167, %t168, %t174)
     //
     // while the callee's body reads field 0 of that first argument and
     // applies it to two ELEMENTS -- so the option instance is handed a
     // dictionary shaped like itself, and the driver dies (exit -1,
     // SIGSEGV in `monad_get_tag`, reached through `apply_closure2`).
     // The two-operand form with a CONCRETE literal on both sides is
     // fine (`Option.some 1 == Option.some 2` emits
     // `number::__Dict_BEq_I64`), which is why this needs the
     // `List.get`-typed operand: the carrier that reaches the class-call
     // pass is the still-generic `Option A`, and the constraint `[BEq A]`
     // is then resolved against the applied carrier rather than its
     // argument. Closed by: fixing that resolution, not by anything in
     // the test file.",
      "the option instance's own dict is passed where its ELEMENT dict belongs -- `some 1 == List.get 0 [1, 2, 3]`",
     // Measured 2026-09-19 (P6): after the applied-head match AND the
     // callee-signature instantiation both landed, `find_matching_instance`
     // agrees on all of these -- what fails is downstream of the match.
     //
     // * dict-arg bindings -- CLOSED for list literals, which is what took
     //   `std/src/list_tests1.mo` off this list and moved
     //   `std/src/list_tests2.mo` onto the codegen bug above. That half was
     //   two bugs: the carrier of a list literal used to be the bare head
     //   `List` (a list literal desugars to `FromListLiteral.cons`, whose
     //   promoted declared type is `A -> List A -> List A` with no Forall
     //   binder at all, so a signature instantiation that only reads
     //   Forall binders found nothing to bind), and a match bound the
     //   instance's own type parameters nowhere. The carrier is now the
     //   instantiated `List I64` and `carrier_bindings` binds the
     //   instance's `A`, so `[Show A]`/`[BEq A]` resolve to the element
     //   dictionary (`__Dict_Show_I64` / `__Dict_BEq_I64`, verified in the
     //   emitted IR).
     // * expected carrier: a call with no carrier-revealing argument at
     //   all (`Map.empty`, `Bounded.max_bound`) never even reaches a
     //   match -- CLOSED for the annotated-let shape (`let m : BTreeMap
     //   I64 I64 := Map.empty` now resolves; that is what took the
     //   checker failure off `std/src/map_tests.mo` and
     //   `std/src/test_map_full.mo`, and off base.mo's `Bounded.max_bound`
     //   -- all three then stopped on a native, and P9 has since wired
     //   the whole f64 family, so all three are off this list entirely).
     //   What still has no channel is a call whose carrier comes
     //   from neither an argument nor an annotation, which is what
     //   `Monad.pure`/`MonadState.modify_get` below are left on: the
     //   enclosing def's own declared return type is consulted for `Monad`
     //   only, and an app ARGUMENT gets no expected type from its callee's
     //   Pi domain (`BEq.beq Bounded.max_bound gt` -- the sibling argument
     //   pins the callee's `A` to `Ordering`; measured in isolation).
     // (list_tests2.mo's own entry was here: the resolution half was
     // CLOSED by the applied-carrier + signature-instantiation work, and
     // the codegen half -- `BEq (List A)` forwarding the element dict to
     // the comparison of the list TAILS -- was closed by P8's D5/D4
     // override plus the already-dict-args guard. Both halves are now
     // verified in the emitted IR: the recursive tail comparison is
     // `BEq_List_A_beq __Dict_BEq_I64 x_tail y_tail`, arity 3.)
     // NOT the same mechanism, and this file is the counter-example
     // worth keeping: the instantiation work does not move it either
     // way. `all_i64`'s `IO.pure (List.empty : List I64)` loses its
     // ascription -- the self-hosted parser's `paren_try_ann` parses
     // `: T` and DROPS it (no `Term.ann` exists) -- so the call's
     // element type is never pinned and reports `expected (IO A), found
     // (IO (List I64))`. That is the expected-type/carrier channel P6
     // owns, alongside `lang/src/json.mo` below.
     "the argument's own ascription is discarded by the self-hosted parser",
     // Same discarded-ascription channel as combine_test.mo above, not
     // type-variable instantiation: the ascriptions on the call (`:
     // Result String Bool`, `: Result String Person`) report `expected
     // A, found <concrete>` because the parser dropped them, which also
     // leaves the match scrutinee's type unknown -- the bare `mk`
     // pattern then reports a constructor ambiguity downstream of the
     // SAME unknown. The Rust host runs all of the file's tests.
     "the call's own ascription is discarded by the self-hosted parser",
     // PARTIALLY CLOSED, and the half that is left is the harder one.
     //
     // The CONSTRUCTOR half is done: `named_call_check_missing_fields`
     // (`lang/typecheck/infer.mo`) no longer demands a field that
     // declares a `:=` default, so `Rect { w := 50 }` is accepted exactly
     // as the bare `{ w := 50 }` literal already was. A default can only
     // exist on a STRUCT's own implicit constructor (`cons_fields_to_params`
     // rejects `:=` on a bare `type`), and `struct_lit_build_args` already
     // substituted it, so the two spellings agreed on the value and
     // disagreed only on whether to accept the omission.
     //
     // What is left is the DEF half, and it is not a policy choice but a
     // missing channel: `ScopeData.def_params` is `List (Pair Identifier
     // Term)` -- name and type, no `Param` -- because it is recovered
     // from the elaborated `Term.lam` chain (`def_params_of_term`,
     // `lang/scope.mo`), and `Term.lam` has no default slot. The parser
     // DOES parse a def param's `:=` (`ParseParam.mk name type_ mult
     // default_ attrs`) and `lam_params_loop` DISCARDS it, so
     // `scale`'s own `factor : I64 := 2` is gone before this path sees
     // the def. Measured, from the self-hosted binary: `error: named
     // call: missing required field `factor` in
     // test_named_call_def_target_uses_declared_default`, the file's only
     // failure -- `test_named_call_constructor_single_field` and
     // `test_named_call_def_target` both pass. Closed by: carrying the
     // default through the parser into the checker (a `Term.lam` field or
     // a parallel `ScopeData` side-table), which touches every
     // `Term.lam` construction site.",
     "a def's own named-call defaults do not survive the parser (`Term.lam` has no default slot)",
     // Same applied-head instance-resolution family as the Map/Show
     // entries above: `Monad.pure`'s only argument is the monad's
     // ELEMENT type, and `MonadState`'s carrier is likewise not
     // recoverable from the call's own arguments.
     "no carrier-revealing argument to infer an instance from",
     "no carrier-revealing argument to infer an instance from",
     // A qualified reference in TARGET position cannot resolve
     // self-hosted, and the blocker is structural rather than a missing
     // case. `build_scope_from_decls` (`lang/scope.mo`) takes ONE
     // `ModulePath` and the pipeline hands it the TARGET's, because
     // `flatten_visible_module_decls` (`lang/module.mo`) has already
     // merged every module's decls into a single list -- as its own doc
     // comment puts it, "each decl's owning module is no longer
     // recoverable". Every dependency def therefore registers with the
     // CONSUMER's module path, so `find_def_by_module_and_name`'s pair
     // match (name == `qn.qname` AND module == `qn.qmod`) can never
     // succeed across a module boundary, however the flattened name is
     // re-split. The DEPENDENCY-position half of the same feature IS
     // fixed (the reference and definition now agree on one symbol
     // spelling, so it no longer dies in `llc`), and the Rust host runs
     // all four of this file's tests. Closed by: routing the pipeline
     // through `build_scope_from_modules` (which preserves per-module
     // identity but is not the path taken today), or carrying each
     // decl's owning module through the flatten -- both touch where
     // `priv` is enforced.",
     "the flatten drops each decl's owning module, so a cross-module qualified ref cannot pair-match"]

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

#[test]
def test_gap_reason_for_listed_path : Bool :=
    String.contains (gap_reason_for "std/src/concurrent/fiber_test.mo") "async runtime"

#[test]
def test_gap_reason_for_unlisted_path_is_empty : Bool :=
    String.beq (gap_reason_for "std/src/list.mo") ""
