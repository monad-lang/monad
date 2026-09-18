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
/// The 21 entries here are what a full corpus sweep
/// actually reports, not a guess, and none is a problem with the test
/// files themselves. In rough order of how much they cost to close:
///
///   * self-hosted checker gaps -- type-variable instantiation, named-
///     call defaults, instance resolution through an applied head
///     (`Show`/`BEq (List A)`, `Map`) or with no carrier-revealing
///     argument at all (`Bounded.max_bound`, `Monad.pure`), and the
///     expected-type channel the parser's discarded ascriptions leave
///     empty (`combine_test.mo`, `json.mo`) -- 12 files;
///   * two codegen bugs -- the generic `Add` dict self-recursion and
///     `BEq (List A)`'s tail dictionary (3 files);
///   * `#[derive]`, unsupported by the self-hosted parser (1 file);
///   * `#[derive_cli]`, whose attribute never reaches a macro (1 file);
///   * `Pred` in value position (1 file);
///   * floating point, which does not exist in the backend (2 files);
///   * the async runtime, which does not exist either (1 file).
///
/// The legacy dotted-path family (~105 call sites across 8 files) that
/// used to head this list is CLOSED: the call sites now import the bare
/// name they call, and both parsers reject a dotted `use` path outright.
///
/// **Matching is on path AND cause**, deliberately: a listed file that
/// starts failing for a NEW reason is reported as a real failure, not
/// excused by its presence here. The cause is matched as a substring of
/// the driver-compile error, so each token below must be harvested from
/// the real binary's own output, never transcribed from prose.
///
/// Three index-aligned `List String`s rather than a list of structs:
/// a user struct constructor inside a list literal miscompiles through
/// the native backend (`TestGap.mk` inside `[...]` emits a call to an
/// undefined `@TestGap.mk` and `llc` rejects the module), while three
/// parallel lists compile and run identically on both backends.
/// `test_gap_lists_are_aligned` guards the alignment the shape gives up.

/// Paths, exactly as the runner reports them (repo-relative; identical
/// whether the user passes a directory or explicit files).
pub def gap_paths : List String :=
    ["init/src/optics_tests.mo",
     "examples/optics.mo",
     "std/src/concurrent/fiber_test.mo",
     "init/src/tests.mo",
     "std/src/sha256_tests.mo",
     "init/src/foldable_tests.mo",
     "init/src/foldable_tests_fold.mo",
     "std/src/base.mo",
     "std/src/derive_tests.mo",
     "std/src/list_tests1.mo",
     "std/src/list_tests2.mo",
     "std/src/map_tests.mo",
     "std/src/test_map_full.mo",
     "std/src/concurrent/combine_test.mo",
     "lang/src/json.mo",
     "cli/src/tests/cli_derive_tests.mo",
     "examples/derive.mo",
     "examples/structs.mo",
     "examples/indexed_monads.mo",
     "examples/state_monad.mo"]

/// The distinguishing substring of each file's own known error.
///
/// Harvested from the real binary's own output, and note that the
/// string differs by WHICH stage fails: a driver-compile error carries
/// the compiler's message, while a link failure and a dead driver are
/// matched against the wording the runner itself prints for them
/// ("compilation failed", "driver exited -1") because llc's own
/// message goes to the console, not into a value the runner holds.
pub def gap_causes : List String :=
    ["native `f64_mul`",
     "native `f64_eq`",
     "native `fork_io`",
     "compilation failed",
     "driver exited -1",
     "driver exited -1",
     "driver exited -1",
     "no instance found for `Bounded.max_bound`",
     "no instance found for `Debug.debug`",
     "no instance found for `Show.show`",
     "no instance found for `BEq.beq`",
     "no instance found for `Map.empty`",
     "no instance found for `Map.empty`",
     "does not typecheck",
     "does not typecheck",
     "does not typecheck",
     "Failed to load",
     "does not typecheck",
     "no instance found for `Monad.pure`",
     "no instance found for `MonadState.modify_get`"]

/// Why each gap is open, and what closes it.
pub def gap_reasons : List String :=
    // Closed by: float support in the backend. Values are boxed i64
    // end to end and there is no f64 anywhere in codegen, so this is a
    // genuine feature, not a wiring gap like the u32/u8 family was.
    ["no floating-point support in the native backend",
     "no floating-point support in the native backend",
     // Closed by: a self-hosted async runtime. Tracked in
     // plans/bootstrapping/self-hosted-async-runtime.md.
     "async runtime not self-hostable yet (fork_io/await_fiber unwired)",
     // Closed by: codegen support for a builtin sort in value position.
     // `init/src/tests.mo:537` uses `Pred` as a value (`get_sort Pred`),
     // which reaches llc as a call to an undefined `@Pred` -- so the
     // driver compiles and the LINK is what fails.
     "builtin sort `Pred` in value position emits an undefined symbol",
     // Closed by: the BEq_List_A_beq dictionary bug -- the element
     // dictionary is applied to the list TAIL, so a `List U8`
     // comparison segfaults. Hashing itself is correct through the
     // native backend (examples/sha256.mo passes, and the empty-string
     // digest matches); only the `List U8` equality in the assertions
     // dies.
     "BEq (List A) applies the element dict to the tail -- segfaults",
     // Closed by: bidirectional inference pushing an expected type into
     // an unannotated lambda parameter. `acc + x` in `Foldable.foldl (fn
     // acc x => acc + x) 0 xs` compiles to the generic forwarding
     // instance `HAdd_A_A_A_add` with the placeholder `__Dict_Add_A`
     // dict, which self-recurses; the same fold with `I64.add` works.
     // The carrier inference that used to fail here IS fixed (the call
     // resolves and the driver builds now) -- this is the next bug
     // behind it.
     "+ on untyped lambda params gets a generic Add dict -- self-recurses",
     "+ on untyped lambda params gets a generic Add dict -- self-recurses",
     // Measured 2026-09-19 (P6, after the applied-head match landed):
     // these six are NOT one bug. `find_matching_instance` now agrees on
     // all of them -- what fails is downstream of the match, and the
     // four names below split into two channels:
     //
     // * dict-arg bindings: a match binds the instance's own type
     //   parameters NOWHERE, so the instance's own constraint (`[Show
     //   A]` on `instance [Show A] Show (List A)`) has no carrier to
     //   resolve against -- and neither does the carrier, which is the
     //   bare head `List` (a list literal desugars to
     //   `FromListLiteral.cons`, whose promoted declared type `A -> List
     //   A -> List A` reveals `List` and drops the element type).
     // * expected carrier: a call with no carrier-revealing argument at
     //   all (`Map.empty`, `Bounded.max_bound`) never even reaches a
     //   match. Annotated lets feed the CHECKER's expected type
     //   (`Enum.from_nat`'s `let f0 : Ordering := ...` in std/src/base.mo
     //   passes) but the codegen pass is not handed one, and an app
     //   ARGUMENT gets no expected type from its callee's Pi domain
     //   (`BEq.beq Bounded.max_bound gt` -- the sibling argument pins the
     //   callee's `A` to `Ordering`; measured in isolation).
     "`Bounded.max_bound` is nullary and `class Bounded` declares no default carrier; the enclosing call's own parameter type (`BEq.beq`'s `A`, pinned to `Ordering` by the sibling argument `gt`) is not threaded into it as an expected carrier",
     "NOT the carrier channel at all -- a macro-DERIVED instance is invisible to this pass. MEASURED via probe: `derive_debug! Point` + `Debug.debug pt` fails identically (`needed in `t_derived``, with no module prefix on the generated def), while the same file with a hand-written `instance Debug Point` passes. Belongs to the `reflect_type_info!`/decl-gen family (P10), not P6",
     "a list literal's carrier is the bare head `List` (the promoted `FromListLiteral.cons` declares `A -> List A -> List A`), so matching succeeds but the instance's own `[Show A]` dict argument has nothing to resolve against: nothing binds `A` to `I64`",
     "same as list_tests1 above, one class over: matching succeeds, the `[BEq A]` dict argument has no bound `A`",
     "`Map.empty` takes no argument, so no carrier is inferred at all, and the annotated binding (`let m : BTreeMap I64 String := Map.empty`) is not handed to it as an expected carrier; even with one, `instance [BOrd K] Map BTreeMap`'s `K` is bound only by the method's own signature (`empty : M K V`), so the `[BOrd K]` dict argument needs signature-vs-carrier bindings too",
     "same as map_tests above: `Map.empty` in an annotated let, `[BOrd K]` unbound",
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
     // Closed by: the attribute-to-macro bridge. The file LOADS -- to
     // the self-hosted parser `#[derive_cli]` is just another
     // `#[name args]` -- but nothing expands it, so the defs it would
     // generate (notably `parse_democommand`) never exist and every test
     // body is an unknown variable. Same family as `examples/derive.mo`
     // below, which dies a stage earlier, at load.
     "`#[derive_cli]` expands to nothing (no attribute-to-macro bridge)",
     // Closed by: `#[derive ...]` support in the self-hosted parser and
     // macro system. The parse stops dead AT the attribute -- an
     // attributed `struct` decl is not accepted, and the remaining-text
     // dump starts on the `#[derive BEq BOrd Debug Lens]` line itself --
     // so nothing downstream ever runs. The declaration-generating
     // macros these attributes dispatch to exist on the host only.
     "#[derive] is not supported by the self-hosted parser",
     // Closed by: named-call argument defaults in the self-hosted
     // checker -- it demands a field the callee declares a default for.
     "named-call defaults are not applied by the self-hosted checker",
     // Same applied-head instance-resolution family as the Map/Show
     // entries above: `Monad.pure`'s only argument is the monad's
     // ELEMENT type, and `MonadState`'s carrier is likewise not
     // recoverable from the call's own arguments.
     "no carrier-revealing argument to infer an instance from",
     "no carrier-revealing argument to infer an instance from"]

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
    is_known_gap "examples/optics.mo" "native `f64_eq` (needed by def `number::F64.beq`) is not wired"

#[test]
def test_is_known_gap_rejects_unknown_cause_on_listed_path : Bool :=
    // The whole point of matching on cause as well as path: this file
    // is listed, but THIS failure is not the one it is listed for.
    Bool.not (is_known_gap "examples/optics.mo" "parse error: unexpected token at 12:3")

#[test]
def test_is_known_gap_rejects_unlisted_path : Bool :=
    Bool.not (is_known_gap "std/src/list.mo" "native `f64_eq` is not wired")

#[test]
def test_gap_reason_for_listed_path : Bool :=
    String.contains (gap_reason_for "std/src/concurrent/fiber_test.mo") "async runtime"

#[test]
def test_gap_reason_for_unlisted_path_is_empty : Bool :=
    String.beq (gap_reason_for "std/src/list.mo") ""
