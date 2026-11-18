/// The lint driver: read a file, parse it with the compiler's own front end,
/// run every rule, and turn the names each rule answered into located
/// diagnostics.
///
/// TWO PARSE CALLS, and each is the compiler's own:
///
///   * `decls_skip` (`lang::parser`) for the `ParseDecl` list the RULES walk.
///     This is the pre-lowering tree, which is where a declaration's
///     `#[...]` attributes still exist: `lower_parse_decl_kind` maps
///     `ParseDeclKind.attrs_d _attrs inner` to its inner declaration, so an
///     attribute on a `use`/`open` is GONE one stage later.
///   * `decl_ranges_of_source` (`lang::module`) for one `SourceRange` per
///     declaration, in source order. This is the compiler's own line/column
///     scan (`resolve_offsets_in_file`), so a lint position and a `check`
///     position for the same declaration cannot disagree.
///
/// `decls_parser_located_with_ranges` would answer both in one call, but its
/// second half is the LOWERED `Decl` list, not the parse tree -- and the
/// rules need the tree. Two parses of the same text is the price of reading
/// the stage that still has attributes.
///
/// ─── `decls_skip` IS ALWAYS CALLED WITH ITS LEADING SKIP ───────────────
///
/// `decls_skip` applies `decl_parser` to its input as-is, and a declaration
/// parser only skips a leading comment if it happens to route through
/// `opt_attributes` -- which is why this was a real, SHAPE-DEPENDENT bug and
/// not a uniform one. Measured on this corpus, with a `/// header` in front
/// of a single declaration:
///
///     type / struct / def / defmacro   bare: 1 declaration   (they skip it)
///     use / open / class / instance / infix
///                                      bare: 0 declarations, text unconsumed
///
/// So every entry point in `lang/parser.mo` does the skipping itself and
/// hands `decls_skip` `skip_docstrings (skip_spaces input)` --
/// `decls_parser`, `decls_parser_located`, `decls_parser_located_cfg` and
/// `decls_parser_located_with_ranges` all spell that same prelude.
///
/// Calling it BARE is not a clean failure either way. `decls_try`'s lenient
/// arm answers SUCCESS carrying whatever it accumulated, so a file that opens
/// with a comment in front of a `use` comes back as `success <whole file>
/// List.empty`: zero declarations, no diagnostic, and a file that lints clean
/// because nothing was ever looked at. Measured: `init/src/view.mo` (5
/// single-constructor types) reported 0 findings bare and 5 with the prelude,
/// and 69 of the 72 files that should have reported were silent.
///
/// `lint_parse` is shaped to make it impossible twice over: the prelude is
/// applied, AND a non-empty remainder is reported as a truncated parse rather
/// than a clean one.
///
/// `decls_skip` RETURNS ITS DECLARATIONS IN SOURCE ORDER -- which is worth
/// stating because the code reads as if it does not. `decls_try` conses onto
/// an accumulator, but each recursive step passes the post-`skip_spaces`
/// REMAINDER, so the text it walks shrinks from the front while `acc` grows
/// from the front: the two reversals cancel. Verified against the real parser
/// on a three-declaration file (`type`/`def`/`type` stayed in that order)
/// before this comment replaced an earlier "it reverses, so un-reverse it"
/// that was measurably wrong and mispaired every range by one.
///
/// The LAST element can be an empty declaration: `decls_try` succeeds once at
/// end-of-input and conses whatever `decl_fail_to_unknown` produced. It
/// contributes no findings, and it is why a fixture ending in `}` parses to
/// one more declaration than it has.
///
/// The ranges are NOT read from `ParseSpan`. A `ParseDecl`'s `start_rem` is
/// where `decls_skip`'s recursion started, which is after the whitespace it
/// skipped -- so it can land on the PREVIOUS declaration's trailing space.
/// `build_loc_table` tolerates that because it looks a `start_rem` up by the
/// same `start_rem`; a driver pairing two lists would not.

use lang::module {DeclRange, decl_range_span, decl_ranges_of_source}
use lang::parser {decls_skip, skip_docstrings}
use lang::parser::whitespace {skip_spaces}
use lang::types {Location, ParseDecl, ParseDeclKind, SourceRange}
use parsec::core {ParseResult}
use lib::config {LintConfig, LintLevel, effective_level, level_name, level_reports}
use lib::diagnostic {LintDiagnostic, mk_lint}
use lib::rules {
    ctor_name_findings, def_name_findings, rule_name_ctor_name_case, rule_name_def_name_case,
    rule_name_single_ctor_type, rule_name_type_name_case, rule_name_type_var_case,
    single_ctor_type_findings, type_name_findings, type_var_findings,
}

// ─── A rule, as a record ───────────────────────────────────────────────
//
// A record with a `check` FIELD, not a `LintRule` class. A class would make
// every rule an instance witness and a heterogeneous registry awkward
// (`List Rule` would have to pass dictionaries as values); a plain record
// plus a static list gives name lookup, a trivial `--list-rules`, and no
// typeclass machinery at all.
//
// `default_level` is per rule because the rules' false-positive rates differ
// by an order of magnitude: `single_ctor_type` has none but ~58 legitimate
// hits in this corpus, so it ships `allow` until a project opts in.

pub struct Rule {
    name : String,
    default_level : LintLevel,
    /// The names this rule rejects for one declaration kind.
    check : ParseDeclKind -> List String,
}

pub def rule_name (r : Rule) : String := r.name

pub def rule_default_level (r : Rule) : LintLevel := r.default_level

/// Apply a rule to one declaration kind.
pub def rule_findings (r : Rule) (k : ParseDeclKind) : List String := (rule_check r) k

pub def rule_check (r : Rule) : ParseDeclKind -> List String := r.check

pub def all_rules : List Rule := [
    Rule.mk rule_name_type_name_case LintLevel.warn type_name_findings,
    Rule.mk rule_name_def_name_case LintLevel.warn def_name_findings,
    Rule.mk rule_name_ctor_name_case LintLevel.warn ctor_name_findings,
    Rule.mk rule_name_type_var_case LintLevel.warn type_var_findings,
    Rule.mk rule_name_single_ctor_type LintLevel.allow single_ctor_type_findings,
]

#[partial]
pub def rule_names_of (rs : List Rule) : List String :=
    match rs {
        List.empty => List.empty,
        List.cons r rest => List.cons (rule_name r) (rule_names_of rest),
    }

pub def rule_names : List String := rule_names_of all_rules

/// One rule as `--list-rules` prints it: `name<TAB>default-level`, a tab so
/// `column -t` lines it up -- which is what a reader deciding what to
/// `--deny` wants.
///
/// This lives in the LIBRARY rather than at either call site on purpose, and
/// the reason is a real bug rather than tidiness: `monad lint` and the
/// standalone `monad-lint` each had their own copy, and they had already
/// drifted -- one printed `name` and the other `name<TAB>level`, from the
/// same registry. That is exactly the disagreement the library-with-a-thin-
/// bin split exists to make impossible, so the rendering is one definition
/// two callers share.
///
/// The pattern match reads all three fields at once: `Rule` holds a function,
/// so calling `rule_name r` and `rule_default_level r` in turn would be two
/// uses of an affine binder.
pub def rule_line (r : Rule) : String :=
    match r {
        Rule.mk name level _check => String.concat_all [name, "\t", level_name level],
    }

#[partial]
pub def rule_lines_of (rs : List Rule) : List String :=
    match rs {
        List.empty => List.empty,
        List.cons r rest => List.cons (rule_line r) (rule_lines_of rest),
    }

/// The whole registry as `--list-rules` prints it, in declaration order.
pub def rule_lines : List String := rule_lines_of all_rules

// ─── Parsing one file ──────────────────────────────────────────────────

/// A file as the linter sees it: its path, its text, the pre-lowering parse
/// the rules walk, and the compiler's per-declaration ranges.
pub struct LintFile {
    path : String,
    source : String,
    parse_decls : List ParseDecl,
    ranges : List DeclRange,
}

pub def lint_file_path (f : LintFile) : String := f.path

pub def lint_file_source (f : LintFile) : String := f.source

pub def lint_file_parse_decls (f : LintFile) : List ParseDecl := f.parse_decls

pub def lint_file_ranges (f : LintFile) : List DeclRange := f.ranges

/// A file's parse, or the reason it was skipped. `lint_failed` carries text
/// because a file that does not parse must be REPORTED and skipped, never
/// linted against a half-built declaration list.
pub type LintParse {
    lint_ok (LintFile),
    lint_failed (String),
}

/// Parse `src` for linting, with the same leading skip every entry point in
/// `lang/parser.mo` applies (`see this module's header`).
///
/// A TRUNCATED walk is a FAILED parse, not a clean one. `decls_skip`'s
/// lenient arm reports success with whatever it reached, so a `success`
/// carrying text it never consumed means `decl_parser` rejected that text --
/// and linting the prefix would report findings about a program the user did
/// not write while silently ignoring the rest of the file. The remainder is
/// compared after the same skip, because it is the leftover declaration text
/// that matters and not the blank lines around it.
///
/// The failure arm short-circuits before the range scan, because a range list
/// over text that did not parse is not worth computing.
pub def lint_parse (path : String) (src : String) : LintParse :=
    match decls_skip (skip_docstrings (skip_spaces src)) List.empty {
        ParseResult.success rem ds =>
            if String.is_empty (skip_docstrings (skip_spaces rem))
            then LintParse.lint_ok (mk_lint_file path src ds)
            else LintParse.lint_failed (parse_failure_message path),
        ParseResult.fail _ => LintParse.lint_failed (parse_failure_message path),
    }

def mk_lint_file (path : String) (src : String) (ds : List ParseDecl) : LintFile :=
    LintFile.mk path src ds (decl_ranges_of_source src)

/// The parse diagnostic this module can give without re-implementing the
/// parser's error rendering. `decls_skip`'s `fail` arm is the END of a
/// lenient walk, not a diagnostic, so the located version belongs to
/// `monad check` -- which already re-parses strictly for exactly this reason.
pub def parse_failure_message (path : String) : String :=
    String.concat path
        " could not be parsed, so it was not linted. Run `monad check` for the located error."

// ─── Pairing declarations with their ranges ────────────────────────────

/// A declaration and the range it occupies. `range` is `none` when the range
/// list ran short -- reported honestly rather than papered over with a
/// zero-width range at the origin.
pub struct Located {
    decl : ParseDecl,
    range : Option SourceRange,
}

pub def located_decl (l : Located) : ParseDecl := l.decl

pub def located_range (l : Located) : Option SourceRange := l.range

/// The first line of a finding's range. `SourceRange.start` is a `Location`
/// already, so no second scan is needed.
pub def located_location (l : Located) : Option Location :=
    match l.range {
        Option.none => Option.none,
        Option.some sr => Option.some sr.start,
    }

/// Zip declarations against ranges. A short `ranges` list yields `none` for
/// the whole tail rather than stopping: every declaration is still linted,
/// and one without a range renders as `<file>:-:-`, which is the honest and
/// visible answer.
///
/// ONE self-recursive def rather than a `pair_decls`/`pair_one` pair. Those
/// two called EACH OTHER, so neither called itself -- which is what the
/// termination checker and `scripts/style_metrics.py`'s
/// `partial_attr_no_self_call` both read, and it forced an unnecessary
/// `#[partial]` on each. Folding the range test into the `List.cons` arm makes
/// the recursion direct, so the attribute goes and the check is a real one
/// again rather than an escape hatch.
pub def pair_decls
    (ds : List ParseDecl) (rs : List DeclRange) (acc : List Located) : List Located :=
    match ds {
        List.empty => reverse_located acc List.empty,
        List.cons d rest =>
            match rs {
                List.empty =>
                    rest_without_ranges rest (List.cons (Located.mk d Option.none) acc),
                List.cons r rrest =>
                    pair_decls rest rrest
                        (List.cons (Located.mk d (Option.some (decl_range_span r))) acc),
            },
    }

/// The tail after the ranges run out: every remaining declaration is still
/// linted, just without a position.
#[partial]
def rest_without_ranges (ds : List ParseDecl) (acc : List Located) : List Located :=
    match ds {
        List.empty => reverse_located acc List.empty,
        List.cons d rest => rest_without_ranges rest (List.cons (Located.mk d Option.none) acc),
    }

#[terminating]
def reverse_located (xs : List Located) (acc : List Located) : List Located :=
    match xs {
        List.empty => acc,
        List.cons x rest => reverse_located rest (List.cons x acc),
    }

pub def located_decls (f : LintFile) : List Located :=
    pair_decls (lint_file_parse_decls f) (lint_file_ranges f) List.empty

/// `Located` is a `ParseDecl` and an `Option SourceRange`, both immutable;
/// a field-wise duplicate is a value copy.
pub instance Copy Located {
    def copy (l : Located) : Pair Located Located :=
        match l {
            mk decl range =>
                let a : Located := { decl := decl, range := range } in
                let b : Located := { decl := decl, range := range } in
                Pair.pair a b,
        }
}

// ─── Running the rules ─────────────────────────────────────────────────

/// Every finding for one located declaration, from every rule.
///
/// The rule is applied to the declaration's KIND, so a rule that does not
/// care about this kind answers `List.empty` -- the no-match arm IS the
/// per-rule kind filter, which is why the registry needs none.
#[partial]
pub def decl_findings
    (path : String) (config : LintConfig) (rules : List Rule) (l : Located)
    (acc : List LintDiagnostic) : List LintDiagnostic :=
    match rules {
        List.empty => acc,
        List.cons rule rest =>
            decl_findings path config rest l
                (List.append acc (one_rule_findings path config rule l)),
    }

/// One rule's findings for one declaration. The level is consulted first, so
/// an `allow`-level rule costs a lookup and nothing else.
///
/// The rule's NAME and LEVEL are threaded rather than the `Rule` record: a
/// `Rule` holds a function, so it is affine and reading three of its fields
/// would be three uses. Its name and default level are the whole of what a
/// diagnostic needs.
def one_rule_findings (path : String) (config : LintConfig) (rule : Rule) (l : Located)
    : List LintDiagnostic :=
    one_rule_at path config (rule_name rule) (rule_default_level rule) (rule_check rule) l

def one_rule_at
    (path : String) (config : LintConfig) (name : String) (default : LintLevel)
    (check : ParseDeclKind -> List String) (l : Located) : List LintDiagnostic :=
    let level : LintLevel := effective_level default config name in
    if Bool.not (level_reports level) then List.empty
    else names_to_diags path name l (check (decl_kind_of l)) List.empty

/// A located declaration's kind, read once.
def decl_kind_of (l : Located) : ParseDeclKind :=
    let d : ParseDecl := located_decl l in d.kind

/// The names a rule rejected, as diagnostics. Each shares the declaration's
/// location: a finding is about the declaration, and `Location`-level spans
/// inside a body are what `Term.ctx` would be needed for.
#[partial]
def names_to_diags
    (path : String) (rule : String) (l : Located) (names : List String)
    (acc : List LintDiagnostic) : List LintDiagnostic :=
    match names {
        List.empty => acc,
        List.cons n rest =>
            let d : LintDiagnostic :=
                mk_lint rule (finding_message rule n) path
                    (located_location l) (finding_help rule) in
            names_to_diags path rule l rest (List.cons d acc),
    }

// ─── Finding text ──────────────────────────────────────────────────────
//
// One message per rule, phrased around the NAME the rule rejected. Kept here
// rather than in `rules.mo` so a rule module stays a pure classifier with no
// prose -- the split `lang/src/typecheck/diagnostic.mo` makes for the
// compiler's own errors.

pub def finding_message (rule : String) (name : String) : String :=
    if String.beq rule rule_name_type_name_case
    then String.concat_all ["type `", name, "` is not UpperCamelCase"]
    else if String.beq rule rule_name_def_name_case
        then String.concat_all ["def `", name, "` is not lower_snake_case"]
    else if String.beq rule rule_name_ctor_name_case
        then String.concat_all ["constructor `", name, "` is not lower_snake_case"]
    else if String.beq rule rule_name_type_var_case
        then String.concat_all ["type variable `", name, "` is not UpperCamelCase"]
    else if String.beq rule rule_name_single_ctor_type
        then String.concat_all ["type `", name, "` has exactly one constructor, so it could be a `struct`"]
    else String.concat_all ["`", name, "` fails `", rule, "`"]

/// The `= help:` line, or `none` when the finding is self-explanatory.
pub def finding_help (rule : String) : Option String :=
    if String.beq rule rule_name_type_name_case
    then Option.some "rename it UpperCamelCase (`SourceRange`, `Functor`)"
    else if String.beq rule rule_name_def_name_case
        then Option.some "rename it lower_snake_case (`mk_param`, `show_loaded_modules`)"
    else if String.beq rule rule_name_ctor_name_case
        then Option.some "rename it lower_snake_case (`some`, `none`, `ok`)"
    else if String.beq rule rule_name_type_var_case
        then Option.some "type variables are CamelCase (`M I J A`) -- AGENTS.md, style rule 2"
    else if String.beq rule rule_name_single_ctor_type
        then Option.some
            "`struct` buys bare `{ f := v }` literals and `{ base with ... }` updates; converting carries the hazard plans/implementations/code-style-and-lint-enforcement.md Phase 7 records"
    else Option.none
