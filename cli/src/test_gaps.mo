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
/// The 17 entries here are what a full `monad test --workspace` sweep
/// actually reports, not a guess: six distinct causes, none of them a
/// problem with the test files themselves. In rough order of how much
/// they cost to close:
///
///   * ~105 legacy dotted-path call sites (mechanical, 2 files here);
///   * two self-hosted checker gaps -- type-variable instantiation, and
///     instance resolution through an applied head or with no
///     carrier-revealing argument (8 files);
///   * two codegen bugs -- the generic `Add` dict self-recursion and
///     `BEq (List A)`'s tail dictionary (3 files);
///   * `Pred` in value position (1 file);
///   * floating point, which does not exist in the backend (2 files);
///   * the async runtime, which does not exist either (1 file).
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
     "lang/src/codegen/test/compile_tests.mo",
     "lang/src/codegen/test/e2e_typecheck_tests.mo",
     "std/src/sha256.mo",
     "std/src/concurrent/combine_test.mo"]

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
     "does not typecheck"]

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
     // Closed by: instance resolution for a method with NO
     // carrier-revealing argument (`Bounded.max_bound` takes none at
     // all), and for an APPLIED instance head (`Show (List A)`,
     // `BEq (List A)`, `Map`): `term_matches_carrier` requires the
     // carrier to be an App when the instance arg is applied, while
     // inference yields a bare head, so element-type propagation is
     // what is actually missing.
     "no carrier-revealing argument to infer an instance from",
     "no carrier-revealing argument to infer an instance from",
     "instance head is applied (Show (List A)); carrier is a bare head",
     "instance head is applied (BEq (List A)); carrier is a bare head",
     "instance head is applied (Map M); carrier is a bare head",
     "instance head is applied (Map M); carrier is a bare head",
     // Closed by: rewriting ~105 legacy dotted-path call sites
     // (`lang.codegen.emit.compile_db_decls_ir` written inline instead
     // of imported) across 8 files. NOT a checker bug -- the paths
     // genuinely name nothing -- and mechanical to fix, but out of
     // scope here.
     "legacy dotted-path call sites name no import",
     "legacy dotted-path call sites name no import",
     // Closed by: type-variable instantiation in the self-hosted
     // checker. Both report a mismatch between a declared `A` and the
     // concrete type at the call (`expected (List A), found (List U8)`;
     // `expected (IO A), found (IO (List I64))`), which the Rust host
     // accepts -- so the files are fine and the checker is not.
     "self-hosted checker does not instantiate a type variable",
     "self-hosted checker does not instantiate a type variable"]

#[partial]
def gap_len (xs : List String) : I64 :=
    match xs {
        List.empty => 0,
        List.cons _ rest => 1 + gap_len rest,
    }

/// Index of `path` in `gap_paths`, or -1. Walks the list rather than
/// using a map: five entries, and the list is expected to shrink.
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
