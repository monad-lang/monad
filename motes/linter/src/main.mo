/// `monad-lint`: the standalone binary, a thin wrapper over the library.
///
/// `monad lint` (the `cli` mote) calls `linter::lint_source` directly, so
/// this binary and that subcommand cannot disagree about what a rule finds --
/// which is the whole reason the work lives in the library. Everything here
/// is argv handling, file reads, rendering and the exit code.
use std::io {IO.read_file, IO.write_stderr}
use std::path {Path}
use clap::parse {Cli.run}
use clap::spec {
    Cli.CommandSpec, Cli.Parsed, Cli.command, Cli.flag, Cli.flag_set, Cli.positional_values,
    Cli.multi_option, Cli.option_values, Cli.positional_multi, Cli.with_args, Cli.with_name,
    Cli.with_version,
}
use linter {
    LintConfig, LintDiagnostic, LintResult, exit_code_of, lint_result_diagnostics,
    lint_result_parse_error, lint_source, rule_level, rule_lines, rule_names,
}
use linter::config {LintLevel, effective_level}
use linter::diagnostic {render_lint, lint_diagnostic_rule}
use linter::driver {Rule, all_rules, rule_default_level, rule_name}

// ─── The command surface ───────────────────────────────────────────────

def spec : Cli.CommandSpec :=
    Cli.with_version "0.1.0"
        (Cli.with_name "monad-lint"
            (Cli.with_args
                [
                    Cli.positional_multi "files" "the .mo files to lint",
                    Cli.multi_option "deny" "" "RULE" "promote a rule to an error (repeatable, comma-separated)",
                    Cli.multi_option "allow" "" "RULE" "silence a rule (repeatable, comma-separated)",
                    Cli.flag "list-rules" "" "print the rule registry and exit",
                    Cli.flag "quiet" "q" "report nothing; the exit code is the answer",
                ]
                (Cli.command "monad-lint" "Report style and hygiene findings in Monad source")))

/// What the caller asked for.
/// Two `List String`s and two `Bool`s, all `Copy`.
pub struct Args {
    files : List String,
    deny : List String,
    allow : List String,
    list_rules : Bool,
    quiet : Bool,
}

pub instance Copy Args {
    def copy (a : Args) : Pair Args Args :=
        match a {
            mk files deny allow list_rules quiet =>
                let x : Args := {
                    files := files, deny := deny, allow := allow,
                    list_rules := list_rules, quiet := quiet } in
                let y : Args := {
                    files := files, deny := deny, allow := allow,
                    list_rules := list_rules, quiet := quiet } in
                Pair.pair x y,
        }
}

def decode (p : Cli.Parsed) : Result String Args :=
    let args : Args := {
        files := Cli.positional_values 0 p,
        deny := split_names (Cli.option_values "deny" p),
        allow := split_names (Cli.option_values "allow" p),
        list_rules := Cli.flag_set "list-rules" p,
        quiet := Cli.flag_set "quiet" p,
    } in
    Result.ok args

// ─── The run ───────────────────────────────────────────────────────────

def run (args : Args) : IO I64 := do {
    if args.list_rules
    then do {
        let _u <- print_rules rule_lines;
        return 0
    }
    else if List.is_empty args.files
        then do {
            IO.write_stderr "monad-lint: no files given\nhint: monad-lint src/lib.mo, or `monad lint` inside a mote\n";
            return 2
        }
        else if args.quiet
            then do {
                // `--quiet` is what a CI job wants: the exit code IS the
                // answer, and a wall of warnings in a log nobody reads is how
                // a gate stops being noticed.
                let config : LintConfig := config_of args;
                let results <- lint_files args.files config List.empty;
                return (exit_code_of config results)
            }
            else do {
                let config : LintConfig := config_of args;
                let results <- lint_files args.files config List.empty;
                let _u <- report_go config results;
                return (exit_code_of config results)
            }
}

/// `--allow`/`--deny` merged into the config. The pipeline spelling keeps the
/// order the flags were declared in readable at the call site.
def config_of (args : Args) : LintConfig :=
    let base : LintConfig := LintConfig.empty in
    let allowed : LintConfig := LintConfig.with_allowed args.allow base in
    LintConfig.with_denied args.deny allowed

/// The registry, via the library's own rendering. Keeping the STRINGS in
/// `linter` rather than here is deliberate: this binary and `monad lint` each
/// used to render the list, and they had already drifted (one printed the
/// name only). One definition, two callers -- see `linter::rule_line`.
#[partial]
def print_rules (lines : List String) : IO Unit := do {
    match lines {
        List.empty => do { return unit },
        List.cons line rest => do {
            let _p : Unit <- IO.println line;
            print_rules rest
        },
    }
}

#[partial]
def lint_files (files : List String) (config : LintConfig) (acc : List LintResult) : IO (List LintResult) := do {
    match files {
        List.empty => do { return List.reverse acc },
        List.cons f rest => do {
            let read <- IO.read_file (Path.path f);
            match read {
                Result.err e => do {
                    IO.write_stderr (String.concat_all ["monad-lint: ", f, ": ", e.message, "\n"]);
                    lint_files rest config acc
                },
                Result.ok src => do {
                    let r : LintResult := lint_source f src config;
                    lint_files rest config (List.cons r acc)
                },
            }
        },
    }
}

#[partial]
def report_go (config : LintConfig) (results : List LintResult) : IO Unit := do {
    match results {
        List.empty => do { return unit },
        List.cons r rest => do {
            let _u <- report_one config r;
            report_go config rest
        },
    }
}

def report_one (config : LintConfig) (r : LintResult) : IO Unit := do {
    match lint_result_parse_error r {
        Option.some msg => do {
            IO.write_stderr (String.concat "error: " (String.concat msg "\n"));
            return unit
        },
        Option.none => do {
            let ds : List LintDiagnostic := lint_result_diagnostics r;
            print_diags config ds
        },
    }
}

#[partial]
def print_diags (config : LintConfig) (ds : List LintDiagnostic) : IO Unit := do {
    match ds {
        List.empty => do { return unit },
        List.cons d rest => do {
            let _p : Unit <- IO.println (render_lint (rule_level config d) d);
            print_diags config rest
        },
    }
}

/// A finding's level: the rule's default, re-levelled by `--allow`/`--deny`.
/// The binary's entry point. `args` is argv AFTER the program name, which is
/// the shape a `[[bin]]` `main` receives -- `motes/docgen/src/main.mo` takes
/// the same parameter, and passing `List.empty` here is what made an early
/// version of this binary print "no files given" no matter what was typed.
def main (args : List String) : IO I64 := Cli.run spec args decode run
// ─── `--deny`/`--allow` as name lists ─────────────────────────────────
//
// Repeatable AND comma-separated, so `--deny a,b` and `--deny a --deny b`
// mean the same thing. `multi_option` already collects the repeats; this
// splits each value.

def split_names (values : List String) : List String :=
    match values {
        List.empty => List.empty,
        List.cons v rest => List.append (split_one v) (split_names rest),
    }

def split_one (s : String) : List String :=
    split_go s 0 0 (String.length s) List.empty

#[terminating]
def split_go (s : String) (i : I64) (from : I64) (n : I64) (acc : List String) : List String :=
    if I64.lt i n
    then
        if is_sep (String.get s i)
        then split_go s (I64.add i 1) (I64.add i 1) n (push_name s from i acc)
        else split_go s (I64.add i 1) from n acc
    else List.reverse (push_name s from n acc)

def is_sep (b : Option U8) : Bool :=
    match b {
        Option.some c =>
            let x : I64 := U8.to_i64 c in
            I64.beq x 44 || I64.beq x 32 || I64.beq x 9,
        Option.none => false,
    }

def push_name (s : String) (from : I64) (stop : I64) (acc : List String) : List String :=
    if I64.lt from stop then List.cons (String.slice s from (I64.sub stop from)) acc else acc
