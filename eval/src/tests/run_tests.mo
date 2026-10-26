/// End-to-end tests for the shared evaluator's filesystem entry, and so for
/// `monad eval`'s exact legacy text. Native only: the fixtures live under
/// `target-monad/eval-tests` (gitignored), and the standard loader reads
/// `init/src` from the repository root, which is `monad test`'s cwd.

use std::path {Path}
use std::process {exec_cmd}
use std::test {Test.write_fixture}
use lib::file {Eval.run_file}

def fixture_dir : String := "target-monad/eval-tests"

def write_fixture (name : String) (source : String) : IO String := do {
    let _ <- exec_cmd "mkdir" ["-p", fixture_dir];
    let path : String := String.concat fixture_dir (String.concat "/" name);
    let _w <- Test.write_fixture (Path.path path) source;
    return path
}

def eval_text (name : String) (source : String) : IO (Result String String) := do {
    let path <- write_fixture name source;
    Eval.run_file path false
}

#[test]
def test_arithmetic_prints_the_legacy_line : IO Bool := do {
    let r <- eval_text "arith.mo" "def main : I64 := 2 + 3\n";
    match r {
        Result.ok text => IO.pure (String.beq text "Eval result 5"),
        Result.err _ => IO.pure false,
    }
}

/// `use` is the standard filesystem loader's job, in `monad eval` as
/// everywhere else: a module outside the ambient prelude resolves.
#[test]
def test_use_resolves : IO Bool := do {
    let r <- eval_text "use.mo" "use init::foldable {}\n\ndef main : I64 := 7\n";
    match r {
        Result.ok text => IO.pure (String.beq text "Eval result 7"),
        Result.err _ => IO.pure false,
    }
}

/// The stage header AND the diagnostics: a failure whose message is empty
/// would print a bare header (the REPL shows the message directly).
#[test]
def test_type_error_keeps_the_legacy_stage_text : IO Bool := do {
    let r <- eval_text "typefail.mo" "def main : I64 := nope\n";
    match r {
        Result.ok _ => IO.pure false,
        Result.err text =>
            IO.pure (String.contains text "FAILED at stage: typecheck"
                && String.contains text "unknown variable"),
    }
}

/// `monad eval` deliberately does NOT add the friendly missing-`main`
/// check: a program without one keeps failing at the stage it always did.
#[test]
def test_missing_main_fails_at_a_stage : IO Bool := do {
    let r <- eval_text "nomain.mo" "def helper : I64 := 1\n";
    match r {
        Result.ok _ => IO.pure false,
        Result.err text => IO.pure (String.contains text "FAILED at stage:"),
    }
}

#[test]
def test_parse_error_is_staged : IO Bool := do {
    let r <- eval_text "parsefail.mo" "def main : I64 := 2 +\n";
    match r {
        Result.ok _ => IO.pure false,
        Result.err text => IO.pure (String.contains text "FAILED at stage:"),
    }
}
