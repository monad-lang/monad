/// One lint finding and how it renders.
///
/// `LintDiagnostic` is deliberately NOT `toolkit::diagnostic`'s
/// `WireDiagnostic`: that type is the WIRE shape (a range in an editor's
/// encoding units, a severity number, no rule name), and every one of its
/// fields would have to be reconstructed here anyway. What the two share is
/// the shape's MEANING, which is what matters for `--json` staying
/// compatible when it lands: `level_severity` already answers the four
/// numbers `WireDiagnostic.severity` carries, so a JSON emitter is a
/// projection and not a second model.
///
/// `location` is an `Option` for the same reason the compiler's own
/// `Diagnostic.range` is (`lang/src/module.mo`): not every finding has a
/// place, and a made-up position is worse than an honest absence -- an
/// editor jumps to the top of the file for a range at the origin, and a
/// user cannot tell that from a real finding on line 1.

use lang::types {Location}
use lib::config {LintLevel}

pub struct LintDiagnostic {
    /// The stable rule identifier, e.g. `unused_open`. This is what
    /// `--allow`/`--deny` name and what `--json` puts in `code`.
    rule : String,
    message : String,
    location : Option Location,
    /// The file the finding is in, as the caller spelled the path. Carried on
    /// the diagnostic rather than kept beside a list of them because the
    /// renderer is the only reader and it needs the two together.
    file : String,
    /// Rendered as `= help: ...` when present.
    help : Option String,
}

/// Every field is an immutable value (`String` and `Option` are `Copy`), so a
/// field-wise duplicate is a value copy. The renderer reads four fields at
/// once, which is a use-count violation without this.
pub instance Copy LintDiagnostic {
    def copy (d : LintDiagnostic) : Pair LintDiagnostic LintDiagnostic :=
        match d {
            mk rule message location file help =>
                let a : LintDiagnostic := {
                    rule := rule, message := message, location := location,
                    file := file, help := help } in
                let b : LintDiagnostic := {
                    rule := rule, message := message, location := location,
                    file := file, help := help } in
                Pair.pair a b,
        }
}

pub def lint_diagnostic_rule (d : LintDiagnostic) : String := d.rule

pub def lint_diagnostic_message (d : LintDiagnostic) : String := d.message

pub def lint_diagnostic_location (d : LintDiagnostic) : Option Location := d.location

pub def lint_diagnostic_file (d : LintDiagnostic) : String := d.file

pub def lint_diagnostic_help (d : LintDiagnostic) : Option String := d.help

/// The one place a finding is constructed, so a new rule cannot forget to
/// fill in `file` or invent a different field order.
pub def mk_lint
    (rule : String) (message : String) (file : String)
    (location : Option Location) (help : Option String) : LintDiagnostic :=
    LintDiagnostic.mk rule message location file help

/// `<file>:<line>:<col>` -- the prefix every human line starts with.
///
/// A finding with no location renders as `<file>:-:-`, which is deliberately
/// ugly: it says the position is missing rather than defaulting to `1:1`,
/// and `grep`-ing for `:-:` finds exactly the rules whose spans need work.
def lint_where (d : LintDiagnostic) : String :=
    String.concat_all [d.file, ":", line_col_of d.location]

def line_col_of (location : Option Location) : String :=
    match location {
        Option.none => "-:-",
        Option.some loc => line_col_at loc,
    }

/// One field read per def: two reads of one `Location` binder is a use-count
/// violation, which is the same shape `lang/src/module.mo`'s
/// `decl_range_name`/`_kind`/`_span` accessors exist for.
def line_col_at (loc : Location) : String :=
    String.concat (I64.to_string (loc_line loc)) (String.concat ":" (I64.to_string (loc_column loc)))

def loc_line (loc : Location) : I64 := loc.line

def loc_column (loc : Location) : I64 := loc.column

/// One finding as two or three lines, in the compiler's own shape:
///
///     warning[unused_open]: imported name `write` is never used
///       --> motes/example/src/lib.mo:12:1
///       = help: remove `write` from the use filter
///
/// The rule name goes in the brackets the compiler already uses for its
/// diagnostic codes, so a reader who knows `error[unknown-variable]` does
/// not have to learn a second convention.
pub def render_lint (level : LintLevel) (d : LintDiagnostic) : String :=
    let header : String := String.concat_all [
        level_prefix level, "[", d.rule, "]: ", d.message,
    ] in
    match d.help {
        Option.none => String.concat header (String.concat "\n  --> " (lint_where d)),
        Option.some h =>
            String.concat_all [
                header, "\n  --> ", lint_where d, "\n  = help: ", h,
            ],
    }

/// `deny` reads as `error`, because that is what it does to the exit code --
/// the same mapping attributes-deprecated-and-cfg gives `#[deny]`.
def level_prefix (level : LintLevel) : String :=
    match level {
        LintLevel.allow => "allow",
        LintLevel.warn => "warning",
        LintLevel.deny => "error",
    }
