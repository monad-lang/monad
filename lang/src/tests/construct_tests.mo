// Tests for `lang/src/construct.mo`: the constructors have to produce
// source that PARSES back, which is what every test here checks.

use lang::types {Decl}
use lib::construct {
    Vis, apps, attr, case, con, con_app, def_of_text, def_text, global, i64,
    if_, lam, match_, param, str, u32, u8, var,
}
use lib::parser {decls_parser}
use lib::pretty {show_term}
use parsec::core {ParseResult}
use std::list {List.intercalate}

// --- Rendering ---

#[test]
def test_str_escapes_quotes : Bool :=
    String.beq (show_term (str "a\"b")) "\"a\\\"b\""

#[test]
def test_app_is_parenthesised : Bool :=
    String.beq (show_term (apps (global "U32.lt") [var 0 "cp", u32 10])) "(U32.lt cp 10u32)"

#[test]
def test_con_prints_qualified : Bool :=
    String.beq (show_term (con_app "Option" "some" [var 0 "x"])) "(Option.some x)"

#[test]
def test_nullary_con_prints_qualified : Bool :=
    String.beq (show_term (con "Option" "none")) "Option.none"

#[test]
def test_match_prints_arms : Bool :=
    let m := match_ (var 0 "x")
        [case "Option.some" ["a"] (global "a"), case "Option.none" [] (global "b")] in
    String.beq (show_term m) "match x {\n Option.some a => a,\n Option.none => b\n}"

#[test]
def test_lam_prints_a_parseable_parameter : Bool :=
    String.beq (show_term (lam "x" (global "U32") (var 0 "x"))) "(fn (x : U32) => x)"

#[test]
def test_numbers_carry_their_suffix : Bool :=
    let parts : List String := [show_term (i64 7), show_term (u32 9), show_term (u8 3)] in
    String.beq (List.intercalate " " parts) "7i64 9u32 3u8"

#[test]
def test_def_text_shape : Bool :=
    let body := if_ (apps (global "U32.lt") [var 0 "cp", u32 10])
        (global "true") (global "false") in
    let text := def_text [attr "partial"] Vis.vis_public "probe"
        [param "cp" (global "U32")] (global "Bool") body in
    String.beq text "#[partial]\npub def probe (cp : U32) : Bool :=\n    if (U32.lt cp 10u32) then true else false\n"

// --- Round trips: rendered source parses back to the same text ---

#[partial]
def round_trips (text : String) : Bool :=
    match decls_parser text {
        ParseResult.success _ decls => one_def_matches text decls,
        ParseResult.fail _ => false,
    }

#[partial]
def one_def_matches (text : String) (decls : List Decl) : Bool :=
    match decls {
        List.cons hd rest =>
            match rest {
                List.empty => def_matches text hd,
                _ => false,
            },
        List.empty => false,
    }

#[partial]
def def_matches (text : String) (decl : Decl) : Bool :=
    match decl {
        Decl.def_d d => String.beq (def_of_text d) text,
        _ => false,
    }

/// The body is a plain name, not `true`: a literal `true` parses as a
/// `Bool` CONSTRUCTOR and the printer spells it back as `Bool.true`.
#[test]
def test_def_round_trips : Bool :=
    round_trips (def_text [attr "partial"] Vis.vis_public "probe"
        [param "cp" (global "U32")] (global "Bool") (global "U32"))

#[test]
def test_two_params_and_no_attrs_round_trip : Bool :=
    round_trips (def_text [] Vis.vis_package "add"
        [param "a" (global "I64"), param "b" (global "I64")] (global "I64")
        (apps (global "I64.add") [var 1 "a", var 0 "b"]))

/// The two literals the entity table needs: an escaped quote/backslash and
/// a real control character.
#[test]
def test_escaped_literal_round_trips : Bool :=
    round_trips (def_text [] Vis.vis_package "e"
        [] (global "Option") (str "a\"b\\c\nd\te"))

/// An astral character must survive as itself, not as a `\u{..}` that a
/// per-byte escaper would have split into invalid UTF-8.
#[test]
def test_astral_literal_round_trips : Bool :=
    round_trips (def_text [] Vis.vis_package "a"
        [] (global "Option") (str "\u{1F600}"))
