/// Known test-runner gaps: files whose test driver cannot be built
/// today, for a reason already understood and recorded here.
///
/// **This file is scaffolding and is expected to reach zero entries and
/// be deleted.** Every entry names the condition that removes it. It
/// exists so that `monad test` can FAIL on an unknown compile failure
/// (the default) while still not failing CI on the handful of known,
/// tracked ones -- before this, every uncompilable file was silently
/// counted as `skipped`, which affects no exit code, so 18 files' worth
/// of tests ran nowhere at all and nothing said so.
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
     "std/src/sha256_tests.mo"]

/// The distinguishing substring of each file's own known error.
pub def gap_causes : List String :=
    ["native `f64_mul`",
     "native `f64_eq`",
     "native `fork_io`",
     "use of undefined value '@Pred'",
     "driver exited -1"]

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
     // which reaches llc as a call to an undefined `@Pred`.
     "builtin sort `Pred` in value position emits an undefined symbol",
     // Closed by: the BEq_List_A_beq dictionary bug -- the element
     // dictionary is applied to the list TAIL, so a `List U8`
     // comparison segfaults. Hashing itself is correct through the
     // native backend (examples/sha256.mo passes, and the empty-string
     // digest matches); only the `List U8` equality in the assertions
     // dies.
     "BEq (List A) applies the element dict to the tail -- segfaults"]

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
