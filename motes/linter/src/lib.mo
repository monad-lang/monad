// The linter mote's library root -- bare `use linter` resolves here.
//
// The pipeline, bottom up: `config` (levels and the `--allow`/`--deny`
// merge), `rules` (one classifier per rule, pure), `diagnostic` (a finding
// and its rendering) and `driver` (the parse, the range pairing and the
// rule dispatch). `lint` is the one entry point a consumer needs.
//
// One type group per module, which is the rule `build/src/lib.mo` set: the
// TYPES are what a consumer cannot get by naming a module it already knows.
// No `{*}` globs.

pub use lib::config {LintConfig, LintLevel}
pub use lib::diagnostic {LintDiagnostic}
pub use lib::driver {
    LintFile, LintParse, Located, Rule,
    all_rules, decl_findings, lint_file_path, lint_parse, located_decls, rule_line,
    rule_lines, rule_name, rule_names,
}
pub use lib::config {effective_level, level_fails, level_reports}
pub use lib::driver {rule_default_level}

use std::list {}
use lib::diagnostic {LintDiagnostic, lint_diagnostic_rule}

// ─── The one entry point ───────────────────────────────────────────────

/// Lint one file's text. Answers the diagnostics to report and whether the
/// file could be parsed at all -- the caller needs the second answer to
/// decide the exit code, because an unparseable input fails the run
/// independently of any lint level.
pub struct LintResult {
    diagnostics : List LintDiagnostic,
    parse_error : Option String,
}

pub def lint_result_diagnostics (r : LintResult) : List LintDiagnostic := r.diagnostics

pub def lint_result_parse_error (r : LintResult) : Option String := r.parse_error

/// Lint `src` as if it were at `path`.
///
/// A file that does not parse is `parse_error := some ...` with NO
/// diagnostics: there is nothing to lint, and reporting findings against a
/// half-built declaration list would be reporting about a program the user
/// did not write.
pub def lint_source (path : String) (src : String) (config : LintConfig) : LintResult :=
    match lint_parse path src {
        LintParse.lint_failed msg => LintResult.mk List.empty (Option.some msg),
        LintParse.lint_ok file =>
            LintResult.mk (lint_file_all config file) Option.none,
    }

/// Every finding in one parsed file, in declaration order.
#[partial]
pub def lint_file_all (config : LintConfig) (file : LintFile) : List LintDiagnostic :=
    lint_file_go file config (located_decls file) List.empty

#[partial]
def lint_file_go (file : LintFile) (config : LintConfig) (ls : List Located)
    (acc : List LintDiagnostic) : List LintDiagnostic :=
    match ls {
        List.empty => acc,
        List.cons l rest =>
            let here : List LintDiagnostic :=
                decl_findings (lint_file_path file) config all_rules l List.empty in
            lint_file_go file config rest (List.append acc here),
    }

/// The exit code for a run's results, given the levels in force.
///
/// `0` clean or warnings only; `1` any deny-level finding OR any parse
/// error. Warnings never fail, matching the compiler's own semantics
/// (`rust-cli/src/main.rs` exits on `error_count` alone).
pub def exit_code_of (config : LintConfig) (results : List LintResult) : I64 :=
    if any_failures config results then 1 else 0

#[partial]
def any_failures (config : LintConfig) (results : List LintResult) : Bool :=
    match results {
        List.empty => false,
        List.cons r rest =>
            if has_parse_error r then true else if has_denied config r.diagnostics then true
            else any_failures config rest,
    }

def has_parse_error (r : LintResult) : Bool :=
    match r.parse_error {
        Option.none => false,
        Option.some _ => true,
    }

#[partial]
def has_denied (config : LintConfig) (ds : List LintDiagnostic) : Bool :=
    match ds {
        List.empty => false,
        List.cons d rest =>
            if level_fails (rule_level config d) then true else has_denied config rest,
    }

/// A finding's level, looked up by its rule name. The diagnostic does not
/// carry the level (the renderer is handed it), so it is recomputed from the
/// registry -- which also means `--deny` on the command line re-levels a
/// finding that a rule emitted at `warn`.
///
/// PUBLIC because both entry points need it: `monad lint` and `monad-lint`
/// each had their OWN copy of this lookup (complete with their own
/// `rule_default_level_of` and a `find_rule` walk), and that is the same
/// duplication that let their `--list-rules` output drift. One definition,
/// so a re-leveling change cannot land in one entry point and not the other.
pub def rule_level (config : LintConfig) (d : LintDiagnostic) : LintLevel :=
    effective_level (rule_default_level_of (lint_diagnostic_rule d)) config (lint_diagnostic_rule d)

def rule_default_level_of (rule : String) : LintLevel :=
    match find_rule all_rules rule {
        Option.none => LintLevel.warn,
        Option.some r => rule_default_level r,
    }

#[partial]
def find_rule (rs : List Rule) (name : String) : Option Rule :=
    match rs {
        List.empty => Option.none,
        List.cons r rest => if String.beq r.name name then Option.some r else find_rule rest name,
    }
