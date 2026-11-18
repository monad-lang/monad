/// Parse-level tests for `lint_parse`.
///
/// WHY THIS FILE EXISTS. The driver used to call `decls_skip src List.empty`
/// BARE, and `decls_skip` applies `decl_parser` to its input as-is. Whether a
/// leading comment is skipped is decided INSIDE each declaration parser, and
/// only the ones routing through `opt_attributes` do it -- measured on this
/// tree, a `/// header` in front of one declaration gives:
///
///     type / struct / def / defmacro   bare: 1 declaration   (they skip it)
///     use / open / class / instance / infix
///                                      bare: 0 declarations, text unconsumed
///
/// `decls_try`'s lenient arm answers SUCCESS there, so the comment-plus-`use`
/// shape came back as "success, zero declarations, the entire file
/// unconsumed" and the linter reported a clean file it had never looked at.
/// Measured on the corpus: 69 of the 72 files that should have reported a
/// `single_ctor_type` finding were silent, and `init/src/view.mo` reported 0
/// where 5 was the answer.
///
/// ─── THE FIXTURES USE `use`/`open` ON PURPOSE ──────────────────────────
///
/// A `type`-based fixture would pass against the BARE call too, because
/// `type_parser` skips a leading comment itself -- so a test built on one
/// would have looked like a regression guard and caught nothing. Every fixture
/// below therefore starts with a declaration form that does NOT self-skip.
/// `test_the_fixture_shape_is_one_that_needs_the_prelude` pins that property,
/// so the guard cannot be defused by rewriting a fixture into a
/// self-skipping shape.
///
/// The file catches the bug from two directions, so a partial regression
/// cannot pass:
///
///   * the `sees_past_*` tests are DIFFERENTIAL -- the same declarations with
///     and without a comment header must parse to the same count;
///   * `test_lint_parse_rejects_a_truncated_walk` requires a file the lenient
///     walk truncates to be reported as a PARSE error rather than linted
///     against the prefix it managed to read.
///
/// All of them read the declarations `lint_parse` hands the rules
/// (`lint_file_parse_decls`), which is exactly the list the bug emptied.
use lang::parser {decls_skip}
use lang::parser::whitespace {skip_spaces}
use lang::parser {skip_docstrings}
use lang::types {ParseDecl}
use parsec::core {ParseResult}
use lib::driver {LintParse, lint_file_parse_decls, lint_parse}

/// The declarations every case is built around: an `open` and a `use`, i.e.
/// the forms whose parsers do NOT skip a leading comment themselves.
def body : String := "use init::copy {Copy}\nopen Id {id}\n"

/// The declarations of `src`, or `-1` when the parse was rejected. A negative
/// sentinel rather than an `Option`: the two arms of `LintParse` carry
/// different payloads, and these tests only need the count.
def decl_count (src : String) : I64 :=
    match lint_parse "t.mo" src {
        LintParse.lint_failed _ => -1,
        LintParse.lint_ok file => List.length (lint_file_parse_decls file),
    }

/// The parse was rejected (its remaining text was not consumed).
def parse_rejected (src : String) : Bool :=
    match lint_parse "t.mo" src {
        LintParse.lint_failed _ => true,
        LintParse.lint_ok _ => false,
    }

/// How many declarations a BARE `decls_skip` call reaches -- the call the bug
/// was. Used only to keep the fixtures honest about what they exercise.
/// Not recursive, so no `#[partial]`.
def bare_decl_count (src : String) : I64 :=
    match decls_skip src List.empty {
        ParseResult.fail _ => -1,
        ParseResult.success _ ds => List.length ds,
    }

// ─── The fixture shape is the one that needs the prelude ───────────────

/// Guards the fixtures themselves. `body` must be a shape that bare
/// `decls_skip` FAILS to walk, or the tests below would pass against the bug
/// and guard nothing. This is the one test that is expected to look redundant
/// and is not: it fails the moment someone "simplifies" a fixture to a `type`.
#[test]
def test_the_fixture_shape_is_one_that_needs_the_prelude : Bool :=
    Bool.not (String.is_empty body) && I64.lt (bare_decl_count (String.concat "/// h\n" body)) 2

/// The other half of the same guard: a form that self-skips (`type`) must NOT
/// be used as a fixture, because bare `decls_skip` would walk it and the test
/// would be vacuous.
#[test]
def test_a_self_skipping_form_is_not_a_useful_fixture : Bool :=
    I64.beq (bare_decl_count "/// h\npub type One { mk }\n") 1

// ─── The header must not hide the file ────────────────────────────────

/// The bug's exact shape: a `///` header in front of a `use` emptied the
/// whole declaration list.
#[test]
def test_lint_parse_sees_past_a_doc_header : Bool :=
    I64.gt (decl_count (String.concat "/// header\n/// more\n" body)) 0

/// Differential: the header changes nothing about what is parsed, which is
/// the statement the bare call violated.
#[test]
def test_lint_parse_header_matches_no_header : Bool :=
    I64.beq (decl_count (String.concat "/// header\n/// more\n/// and more\n" body)) (decl_count body)

/// A plain `//` header is skipped by the same prelude (`skip_docstrings`
/// matches `//` as a prefix of `///`), and it was equally invisible before.
#[test]
def test_lint_parse_sees_past_a_line_comment : Bool :=
    I64.beq (decl_count (String.concat "// a plain comment\n" body)) (decl_count body)

/// A blank-line/whitespace prefix, the case the `skip_spaces` half covers.
#[test]
def test_lint_parse_sees_past_leading_blank_lines : Bool :=
    I64.beq (decl_count (String.concat "\n\n   \n" body)) (decl_count body)

/// Both halves together, in the order the parser's entry points use them.
#[test]
def test_lint_parse_sees_past_a_comment_after_blank_lines : Bool :=
    I64.beq (decl_count (String.concat "\n\n// after blanks\n/// and a doc line\n" body)) (decl_count body)

/// A header in front of EACH form the prelude has to cover, so the guard is
/// not accidentally specific to the first declaration in the fixture.
#[test]
def test_lint_parse_sees_past_a_header_on_every_form : Bool :=
    let _a : Bool := I64.beq (decl_count "/// h\nopen Id {id}\n") (decl_count "open Id {id}\n") in
    let _b : Bool := I64.beq (decl_count "/// h\nuse init::copy {Copy}\n") (decl_count "use init::copy {Copy}\n") in
    let _c : Bool := I64.beq (decl_count "/// h\nclass C A { def m : A }\n") (decl_count "class C A { def m : A }\n") in
    _a && _b && _c

// ─── A truncated walk is not a clean file ─────────────────────────────

/// The lenient arm answers `success` carrying whatever it reached, so a
/// non-empty remainder is the only signal that text was NOT parsed. Linting
/// the prefix would report findings about a program the user did not write,
/// so it must be a parse error instead.
#[test]
def test_lint_parse_rejects_a_truncated_walk : Bool :=
    parse_rejected (String.concat body "}}}\n")

/// A file that parses completely is NOT rejected -- the guard above must not
/// turn every file into an error.
#[test]
def test_lint_parse_accepts_a_whole_file : Bool :=
    Bool.not (parse_rejected (String.concat "/// header\n" body))

/// Trailing blank lines are not "remaining text": the remainder is compared
/// after the same skip the parse applied, or every file ending in a newline
/// would report a parse error.
#[test]
def test_lint_parse_ignores_trailing_whitespace : Bool :=
    Bool.not (parse_rejected (String.concat body "\n\n   \n"))

/// Trailing comments are consumed as whitespace by the same skip, so they are
/// not a truncated parse either.
#[test]
def test_lint_parse_ignores_a_trailing_comment : Bool :=
    Bool.not (parse_rejected (String.concat body "// nothing after this\n"))
