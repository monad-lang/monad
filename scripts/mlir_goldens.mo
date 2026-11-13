// `mlir-goldens`: print every golden module from
// `mlir/src/tests/golden_modules.mo`, so `scripts/check-mlir-goldens.sh`
// can byte-compare it against the checked-in `.mlir` file beside it.
//
//   monad script mlir-goldens                # every golden, to stdout
//   monad script mlir-goldens --list         # just the names, one per line
//   monad script mlir-goldens --name GOLDEN  # one golden, to stdout
//
// NOTHING IS WRITTEN TO DISK. The script is a pure `(name, module)` source;
// the shell script owns the file comparison, because that is where
// `mlir-opt` also lives and keeping the diff message and the tool
// invocation adjacent is what makes a failure readable.
//
// WHY A SCRIPT AND NOT A `#[test]`. The goldens are reachable two ways:
// `monad test mlir` (in-process, over `mlir/src/tests/`) and this script
// plus `scripts/check-mlir-goldens.sh` (the half that needs `mlir-opt`).
// The second cannot be a `#[test]` on a machine without MLIR, and a
// `#[test]` that skips itself silently is exactly what Phase 0's
// `--require` was added to prevent. A script is opt-in by construction.
//
// WHY THE MODULES LIVE IN `mlir/src/tests/` AND NOT HERE. They are the
// mote's own fixtures, so the in-process test asserts their text with no
// subprocess; this file is a thin renderer over them. A golden written here
// only would be invisible to `monad test mlir`.
//
// NO `clap`. `bootstrap_next.mo` uses `clap::spec` because it has eight
// flags and wants generated `--help`; this has two and wants to run on a
// machine that has nothing but `std`. A `[script-dependencies]` entry would
// make a compiler mote a dependency of the one script whose job is to prove
// the emitter needs no front end at all.

open IO {println, write_stderr}
use mlir::print {print_module}
use mlir::tests::golden_modules {golden_module, golden_names, show_names}

/// What the command line asked for.
///
/// `struct`, not a single-constructor `type`: this compiler gives a one-arm
/// inductive no record literal (`ConsName { .. }` is the spelling there), and
/// a two-flag options record wants the struct form.
pub struct Args {
    list_only : Bool,
    /// `Option.some` when `--name` was given. An empty `--name` is rejected
    /// rather than treated as "no name": a caller asking for a golden that
    /// does not exist must get exit 1, not an empty stream and exit 0.
    name : Option String,
}

/// `Copy` because `parse_args` threads the accumulator through every
/// argument, and `run` then reads two fields off it: an affine record would
/// need a destructuring match in each, which reads worse than the derived
/// copy for a two-field bag of scalars.
pub instance Args_copy : Copy Args {
    def copy (a : Args) : Pair Args Args := Pair.pair a a
}

def default_args : Args := { list_only := false, name := Option.none }

/// `acc` with `--list` set. Two tiny helpers rather than `{ acc with ... }`
/// inline, because the record-update form at each call site is what made
/// the earlier version's `Args` un-inferrable.
def Args.with_list_only (acc : Args) : Args :=
    { list_only := true, name := acc.name }

/// `acc` with `--name n`.
def Args.with_name (acc : Args) (n : String) : Args :=
    { list_only := acc.list_only, name := Option.some n }

/// `--list`, `--name GOLDEN`, or a usage error.
def parse_args (argv : List String) (acc : Args) : Result String Args :=
    match argv {
        List.empty => Result.ok acc,
        List.cons a rest =>
            if String.beq a "--list" then
                parse_args rest (Args.with_list_only acc)
            else if String.beq a "--name" then parse_named rest acc
            else Result.err (String.concat "unknown argument: " a),
    }

/// `--name` consumes the next word; a missing one is a usage error.
def parse_named (rest : List String) (acc : Args) : Result String Args :=
    match rest {
        List.empty => Result.err "--name needs a golden name",
        List.cons n more => parse_args more (Args.with_name acc n),
    }

/// One golden's rendered text, or a diagnostic naming it.
def render_one (name : String) : IO I64 := do {
    match golden_module name {
        Option.some m => do {
            // `write_stdout`, not `println`: the module text already ends in
            // a newline, and a second one would make every golden differ
            // from its file by a blank line -- a diff nobody wants to read.
            IO.write_stdout (print_module m);
            return 0
        },
        Option.none => do {
            write_stderr (String.concat "no such golden: " (String.concat name "\n"));
            return 1
        },
    }
}

/// Every golden, each preceded by a `// === <name> ===` marker so one
/// stream carries all of them and the shell script can split it without a
/// second process per golden.
///
/// The marker is a `//` comment, so a stream the splitter failed on is
/// still PARSEABLE MLIR -- which matters because the first thing the script
/// does with each extracted chunk is hand it to `mlir-opt`.
def report_each (names : List String) : IO I64 := do {
    match names {
        List.empty => return 0,
        List.cons n rest => do {
            println (String.concat "// === " (String.concat n " ==="));
            let code <- render_one n;
            if I64.beq code 0 then report_each rest else return code
        },
    }
}

/// After argv is parsed.
def run (args : Args) : IO I64 :=
    if args.list_only then do {
        println (show_names golden_names);
        return 0
    } else match args.name {
        Option.some n => render_one n,
        Option.none => report_each golden_names,
    }

pub def main (argv : List String) : IO I64 :=
    match parse_args argv default_args {
        Result.ok args => run args,
        Result.err message => do {
            writeln_err message;
            writeln_err "usage: monad script mlir-goldens [--list] [--name GOLDEN]";
            return 2
        },
    }

def writeln_err (line : String) : IO Unit :=
    write_stderr (String.concat line "\n")
