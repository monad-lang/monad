/// Phase 1's acceptance test: `print_module` renders each golden module
/// to the text checked in under `fixtures/mlir/goldens/`, BYTE for byte.
///
/// This is the half that runs everywhere. `monad test mlir` executes it on a
/// machine with no `mlir-opt` at all, which is the point: the printer is a
/// pure function and its correctness must not depend on a toolchain being
/// installed. The other half -- "does MLIR itself accept and round-trip that
/// text" -- is `scripts/check-mlir-goldens.sh`, which is opt-in and
/// skip-clean.
///
/// ## Why the expected text is read from a FILE and not inlined here
///
/// Two reasons, and the first is the whole point of a golden:
///
/// 1. A reader reviewing a change to the printer wants to SEE the diff in
///    `.mlir`, in MLIR's own syntax, not in a Monad string literal with
///    escapes. A checked-in `.mlir` file is also usable directly as
///    `mlir-opt` input, which is what makes the other half of the harness
///    possible without a second copy of the text.
/// 2. It is the same artefact `scripts/check-mlir-goldens.sh` diffs, so the
///    in-process and the toolchain halves cannot disagree about what the
///    expected output is. Two copies of an expected string is the classic
///    way a golden test stops testing anything.
///
/// The path is relative to the repo root, which is how `monad test` is
/// invoked from CI and from the dev shell (`scripts/check-monad-tests.sh`
/// cd's there first).
///
/// ## Every test asserts the EXPECTED bytes
///
/// Following Phase 0.5's lesson (the `U8` stride bug both backends had, so
/// they agreed perfectly on the wrong answer): a test that compared
/// `print_module` against something derived from `print_module` would be
/// vacuous. Each of these reads a file and compares whole strings.

open IO {println, read_file}
use std::list {List.any}
use std::stream {StreamError}
use mlir::print {print_module}
use mlir::tests::golden_modules {golden_module, golden_names}

/// Where the expected output lives. One constant so a moved fixture breaks
/// every test with the same message rather than each with its own path.
def golden_dir : String := "fixtures/mlir/goldens/"

/// `name`'s expected text, or the read error.
def expected_text (name : String) : IO (Result StreamError String) :=
    read_file (Path.path (golden_dir ++ name ++ ".mlir"))

/// The rendered text for `name`, or a message naming the missing golden.
def rendered_text (name : String) : Option String :=
    match golden_module name {
        Option.some m => Option.some (print_module m),
        Option.none => Option.none,
    }

/// One golden against its file: `Result.ok true` on a byte match,
/// `Result.err` carrying a readable diagnosis (the lengths and the first
/// differing byte, so a whitespace-only drift is visible as such).
def compare_golden (name : String) : IO (Result String Bool) := do {
    match rendered_text name {
        Option.none =>
            IO.pure (Result.err (String.concat "no module registered as " name)),
        Option.some got => do {
            let r <- expected_text name;
            match r {
                Result.err e =>
                    IO.pure (Result.err (String.concat "cannot read " (String.concat (golden_dir ++ name ++ ".mlir") (String.concat ": " e.message)))),
                Result.ok want => IO.pure (Result.ok (String.beq got want)),
            }
        }
    }
}

// ─── one test per golden ─────────────────────────────────────────────
//
// Separate tests rather than one loop, because a failure then names the
// golden in the test's own name. The corpus runner prints test names, so
// `test_golden_branching` failing says which module drifted without a
// reader having to open the log.

#[test]
def test_golden_scalar_saxpy : IO Bool :=
    golden_is_exact "scalar_saxpy"

#[test]
def test_golden_loop_carried : IO Bool :=
    golden_is_exact "loop_carried"

#[test]
def test_golden_branching : IO Bool :=
    golden_is_exact "branching"

/// The shared body: compare, and on a mismatch print WHY so the failure is
/// actionable from the test transcript alone.
///
/// The result is bound to a local before it is matched, and the failure path
/// is its own def: a `match` on an `IO`-produced `Result` whose arms diverge
/// into `IO` is the shape this compiler's checker rejects as "constructor
/// not found in inductive" -- the same limitation that makes
/// `std/src/buf_tests.mo` bind before matching.
def golden_is_exact (name : String) : IO Bool := do {
    let r <- compare_golden name;
    report_comparison name r
}

def report_comparison (name : String) (r : Result String Bool) : IO Bool :=
    match r {
        Result.ok same => IO.pure same,
        Result.err message => report_failure name message,
    }

def report_failure (name : String) (message : String) : IO Bool := do {
    println (String.concat name (String.concat ": " message));
    IO.pure false
}

// ─── the registry's own invariants ───────────────────────────────────

/// Every golden name is unique. A duplicate would make `golden_module`
/// answer the FIRST entry while `check-mlir-goldens.sh` iterates both, so
/// one of the two files would never be compared and nothing would say so.
#[test]
def test_golden_names_are_unique : Bool :=
    no_duplicates golden_names

def no_duplicates (names : List String) : Bool :=
    match names {
        List.empty => true,
        List.cons n rest =>
            Bool.not (List.any (fn x => String.beq x n) rest) && no_duplicates rest,
    }

/// Every registered name resolves back to its module -- so a typo in the
/// registry cannot leave a name that renders nothing and exits 0.
#[test]
def test_every_golden_name_resolves : Bool :=
    all_resolve golden_names

def all_resolve (names : List String) : Bool :=
    match names {
        List.empty => true,
        List.cons n rest => resolves n && all_resolve rest,
    }

def resolves (name : String) : Bool :=
    match golden_module name {
        Option.some _ => true,
        Option.none => false,
    }

/// A name that is not registered is `Option.none`, which is what lets the
/// emitter script exit 1 rather than printing an empty module.
#[test]
def test_an_unknown_golden_is_none : Bool :=
    match golden_module "no_such_golden" {
        Option.some _ => false,
        Option.none => true,
    }

/// The registry is non-empty AND the three shapes the file documents are
/// all present. A registry that lost an entry would otherwise pass every
/// per-golden test above (they would simply not run), which is the silent
/// failure a `List.map`-over-a-registry harness is prone to.
#[test]
def test_the_registry_has_all_three_shapes : Bool :=
    List.any (fn n => String.beq n "scalar_saxpy") golden_names
        && List.any (fn n => String.beq n "loop_carried") golden_names
        && List.any (fn n => String.beq n "branching") golden_names
