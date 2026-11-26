/// Rule tests: source string in, the names a rule rejects out.
///
/// These are PURE -- no files, no IO -- which is why `rules.mo` classifies by
/// `ParseDeclKind` and hands back strings instead of diagnostics. The
/// end-to-end path (parse, locate, render) is `lint_source`'s and is
/// exercised through the binary.
use lang::types {ParseDecl, ParseDeclKind}
use lang::parser {decls_skip}
use parsec::core {ParseResult, Text}
use lib::rules {
    ctor_name_findings, def_name_findings, is_lower_snake, is_upper_camel, single_ctor_type_findings,
    type_name_findings, type_var_findings,
}

/// The declaration kinds of `src`, in source order -- which is the order
/// `decls_skip` already answers in (see `driver.mo`'s note on why the
/// accumulator does not reverse it).
def kinds_of (src : String) : List ParseDeclKind :=
    match decls_skip (Text.of_string src) List.empty {
        ParseResult.success _ ds => List.map kind_of ds,
        ParseResult.fail _ => List.empty,
    }

def kind_of (d : ParseDecl) : ParseDeclKind := d.kind

/// Every finding of one rule over every declaration in `src`.
#[partial]
def findings_of (rule : ParseDeclKind -> List String) (ks : List ParseDeclKind)
    (acc : List String) : List String :=
    match ks {
        List.empty => acc,
        List.cons k rest => findings_of rule rest (List.append acc (rule k)),
    }

/// Joined with commas so a failure message shows what was found.
#[terminating]
def joined (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons x rest => if List.is_empty rest then x else String.concat x (String.concat "," (joined rest)),
    }

// ─── The case classifiers themselves ──────────────────────────────────

#[test]
def test_upper_camel_accepts : Bool :=
    is_upper_camel "SourceRange" && is_upper_camel "Functor" && is_upper_camel "M"

#[test]
def test_upper_camel_rejects : Bool :=
    Bool.not (is_upper_camel "source_range") && Bool.not (is_upper_camel "_Private")
        && Bool.not (is_upper_camel "")

#[test]
def test_lower_snake_accepts : Bool :=
    is_lower_snake "mk_param" && is_lower_snake "s" && is_lower_snake "_private"

#[test]
def test_lower_snake_rejects : Bool :=
    Bool.not (is_lower_snake "MkParam") && Bool.not (is_lower_snake "")

// ─── type_name_case ───────────────────────────────────────────────────

#[test]
def test_type_name_case_flags_lowercase_type : Bool :=
    String.beq (joined (findings_of type_name_findings (kinds_of "type bad_name { mk }\n") List.empty))
        "bad_name"

#[test]
def test_type_name_case_accepts_upper : Bool :=
    List.is_empty (findings_of type_name_findings (kinds_of "type GoodName { mk }\n") List.empty)

/// Both kinds report, and the assertion is SET membership rather than one
/// joined string: `decls_skip`'s declaration ORDER for a multi-declaration
/// fixture is its walk's business, not this rule's, and pinning the order
/// here would make the test fail for a reason that is not a lint defect.
#[test]
def test_type_name_case_covers_struct_and_class : Bool :=
    let src : String := "struct bad_struct { x : I64 }\nclass bad_class A { def m : A }\n\n" in
    let got : List String := findings_of type_name_findings (kinds_of src) List.empty in
    Bool.and (contains_str "bad_struct" got) (contains_str "bad_class" got)

#[terminating]
def contains_str (x : String) (xs : List String) : Bool :=
    match xs {
        List.empty => false,
        List.cons y rest => String.beq x y || contains_str x rest,
    }

// ─── def_name_case ────────────────────────────────────────────────────

#[test]
def test_def_name_case_flags_camel : Bool :=
    String.beq (joined (findings_of def_name_findings (kinds_of "def BadDef : I64 := 1\n") List.empty))
        "BadDef"

#[test]
def test_def_name_case_accepts_snake : Bool :=
    List.is_empty (findings_of def_name_findings (kinds_of "def good_def : I64 := 1\n") List.empty)

/// A dotted name is judged on its LAST segment: `def List.length` is a
/// lower_snake name bound into `List`, not a `List`-shaped def name.
#[test]
def test_def_name_case_judges_the_last_segment : Bool :=
    List.is_empty (findings_of def_name_findings (kinds_of "def List.length : I64 := 1\n") List.empty)

#[test]
def test_def_name_case_flags_a_capitalised_last_segment : Bool :=
    String.beq (joined (findings_of def_name_findings (kinds_of "def List.Length : I64 := 1\n") List.empty))
        "List.Length"

/// A `#[native]` def's name comes from the C side, so the convention is not
/// the author's to keep.
#[test]
def test_def_name_case_skips_native : Bool :=
    List.is_empty
        (findings_of def_name_findings
            (kinds_of "#[native \"monad_Thing\"]\ndef Thing (x : I64) : I64\n") List.empty)

// ─── ctor_name_case ───────────────────────────────────────────────────

#[test]
def test_ctor_name_case_flags_capitalised_ctor : Bool :=
    String.beq (joined (findings_of ctor_name_findings (kinds_of "type T { Some (a : I64), none }\n") List.empty))
        "Some"

#[test]
def test_ctor_name_case_accepts_lowercase : Bool :=
    List.is_empty (findings_of ctor_name_findings (kinds_of "type T { some, none }\n") List.empty)

/// An `#[opaque]` native-backed type's witness is lower_snake, so it passes;
/// the point of the test is that a NATIVE carrier is not itself skipped --
/// its constructors are still the author's names.
#[test]
def test_ctor_name_case_flags_a_bad_ctor_on_an_opaque_type : Bool :=
    String.beq
        (joined (findings_of ctor_name_findings
            (kinds_of "#[opaque]\ntype Handle { Handle_witness }\n") List.empty))
        "Handle_witness"

// ─── type_var_case ────────────────────────────────────────────────────

#[test]
def test_type_var_case_flags_lowercase_var : Bool :=
    String.beq (joined (findings_of type_var_findings (kinds_of "type Box a { box (a : a) }\n") List.empty))
        "a"

#[test]
def test_type_var_case_accepts_camel : Bool :=
    List.is_empty (findings_of type_var_findings (kinds_of "type Box A { box (a : A) }\n") List.empty)

/// A class's PARAMS are type variables, so a lowercase one is flagged. Note
/// the trailing blank line: `class_parser` needs the declaration to end, and
/// a file with no line after the closing `}` parses to nothing -- the fixture
/// this test used to carry failed for exactly that reason, not because the
/// rule was wrong.
#[test]
def test_type_var_case_covers_class_params : Bool :=
    String.beq
        (joined (findings_of type_var_findings (kinds_of "class Good a { def m : a }\n\n") List.empty))
        "a"

// ─── single_ctor_type ─────────────────────────────────────────────────

#[test]
def test_single_ctor_type_flags_one_ctor : Bool :=
    String.beq
        (joined (findings_of single_ctor_type_findings (kinds_of "type One { mk (x : I64) }\n") List.empty))
        "One"

#[test]
def test_single_ctor_type_accepts_two_ctors : Bool :=
    List.is_empty
        (findings_of single_ctor_type_findings (kinds_of "type Two { some, none }\n") List.empty)

#[test]
def test_single_ctor_type_ignores_struct : Bool :=
    List.is_empty
        (findings_of single_ctor_type_findings (kinds_of "struct S { x : I64 }\n") List.empty)
// ─── type_var_case judges TYPE variables, not value parameters ─────────
//
// The first end-to-end run flagged `(x : I64)` as a badly-named type
// variable, which would have reported every ordinary argument binder in the
// corpus. A param is a type variable only when its declared type is a sort.

#[test]
def test_type_var_case_ignores_value_params : Bool :=
    List.is_empty
        (findings_of type_var_findings
            (kinds_of "def f (x : I64) (name : String) : I64 := x\n") List.empty)

#[test]
def test_type_var_case_ignores_function_params : Bool :=
    List.is_empty
        (findings_of type_var_findings
            (kinds_of "def g (f : A -> B) : A -> B := f\n") List.empty)

/// The higher-kinded shape: `M : Type -> Type` IS a type variable, so a
/// lowercase one is reported.
#[test]
def test_type_var_case_catches_a_lowercase_kind_variable : Bool :=
    String.beq
        (joined (findings_of type_var_findings
            (kinds_of "class Box (m : Type -> Type) { def wrap : m I64 }\n\n") List.empty))
        "m"
