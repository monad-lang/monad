/// Behavioural tests for the formatter: canonical spacing, indentation,
/// comment preservation, idempotence, and the parser-sensitive tight pairs.

use lib::fmt { Fmt.default_config, Fmt.format_source }

def fmt (src : String) : String :=
    match Fmt.format_source Fmt.default_config src {
        Result.ok out => out,
        Result.err _ => "<error>",
    }

def expect (src : String) (want : String) : Bool :=
    String.beq (fmt src) want

#[test]
def test_empty_stays_empty : Bool :=
    expect "" ""

#[test]
def test_adds_final_newline : Bool :=
    expect "def a : I64 := 1" "def a : I64 := 1\n"

#[test]
def test_canonical_spacing : Bool :=
    expect "def f (a : I64) : I64 := a+1\n" "def f (a : I64) : I64 := a + 1\n"

#[test]
def test_tightens_openers_and_closers : Bool :=
    expect "def f : I64 := g( x , y )\n" "def f : I64 := g (x, y)\n"

#[test]
def test_single_line_braces : Bool :=
    expect "def p : Point := {x:=1,y:=2}\n" "def p : Point := { x := 1, y := 2 }\n"

#[test]
def test_indents_one_level : Bool :=
    expect "def f : I64 :=\n  1\n" "def f : I64 :=\n    1\n"

#[test]
def test_tabs_become_four_spaces : Bool :=
    expect "def f : I64 :=\n\t1\n" "def f : I64 :=\n    1\n"

#[test]
def test_closer_aligns_with_opener_line : Bool :=
    expect
        "def f : I64 :=\n    match x {\n        some a => a,\n        none => 0\n    }\n"
        "def f : I64 :=\n    match x {\n        some a => a,\n        none => 0\n    }\n"

#[test]
def test_blank_runs_are_capped : Bool :=
    expect
        "def a : I64 := 1\n\n\n\ndef b : I64 := 1\n"
        "def a : I64 := 1\n\ndef b : I64 := 1\n"

#[test]
def test_negative_literal_adjacency_is_preserved : Bool :=
    expect "def a : I64 := b -1\n" "def a : I64 := b -1\n"

#[test]
def test_subtraction_keeps_its_space : Bool :=
    expect "def a : I64 := b- 1\n" "def a : I64 := b - 1\n"

#[test]
def test_no_space_subtraction_stays_applied_negative : Bool :=
    expect "def a : I64 := b-1\n" "def a : I64 := b -1\n"

#[test]
def test_dotted_name_is_tight : Bool :=
    expect "def f (x : T) : U := x . y\n" "def f (x : T) : U := x . y\n"

#[test]
def test_dotted_name_stays_tight : Bool :=
    expect "def f (x : T) : U := x.y\n" "def f (x : T) : U := x.y\n"

#[test]
def test_macro_suffix_is_tight : Bool :=
    expect "def f : X := foo !\n" "def f : X := foo !\n"

#[test]
def test_macro_suffix_stays_tight : Bool :=
    expect "def f : X := foo!\n" "def f : X := foo!\n"

#[test]
def test_attribute : Bool :=
    expect "#[test]\ndef f : Bool := true\n" "#[test]\ndef f : Bool := true\n"

#[test]
def test_infix_declaration : Bool :=
    expect "infix(++) := List.append\n" "infix (++) := List.append\n"

#[test]
def test_line_comment_preserved : Bool :=
    expect "// hi\ndef f : I64 := 1\n" "// hi\ndef f : I64 := 1\n"

#[test]
def test_trailing_comment_kept_on_line : Bool :=
    expect "def f : I64 := 1 //  note  \n" "def f : I64 := 1 //  note\n"

#[test]
def test_raw_string_is_one_token : Bool :=
    expect "def f : String := r#\"a + b\"#\n" "def f : String := r#\"a + b\"#\n"

#[test]
def test_crlf_becomes_lf : Bool :=
    expect "def f : I64 := 1\r\n" "def f : I64 := 1\n"

/// `String.drop 1` lands mid-character on a multi-byte codepoint and returns
/// ""; arbitrary-text scanners must step by a whole character.
#[test]
def test_unicode_in_string : Bool :=
    expect "def k : String := \"ꟛ\"\n" "def k : String := \"ꟛ\"\n"

#[test]
def test_unicode_in_comment : Bool :=
    expect "// ꟛ in a comment\ndef f : I64 := 1\n" "// ꟛ in a comment\ndef f : I64 := 1\n"

#[test]
def test_unicode_char_literal : Bool :=
    expect "def k : Char := 'ꟛ'\n" "def k : Char := 'ꟛ'\n"

/// `return (match x {` opens a paren and a brace on one line. The arms are
/// one level below that line, not one level below a count of every opener.
#[test]
def test_opener_and_brace_on_one_line : Bool :=
    let want : String :=
        "def f : I64 := do {\n    return (match x {\n        some a => a,\n        none => 0,\n    })\n}\n" in
    let messy : String :=
        "def f : I64 := do {\nreturn (match x {\nsome a => a,\nnone => 0,\n})\n}\n" in
    String.beq (fmt messy) want && String.beq (fmt (fmt messy)) want

#[test]
def test_idempotent : Bool :=
    let once : String := fmt "def f (a : I64) : I64 := a+1\n" in
    String.beq (fmt once) once

#[test]
def test_idempotent_braces : Bool :=
    let once : String := fmt "def f : I64 :=\n\tmatch x {some a => a,none => 0}\n" in
    String.beq (fmt once) once

/// A scale check: the lexer threads suffixes rather than absolute indices, so
/// this stays linear. It also protects the renderer's output shape.
#[test]
def test_many_lines : Bool :=
    let src : String := String.repeat "def f (a : I64) : I64 := a+1\n" 400 in
    let want : String := String.repeat "def f (a : I64) : I64 := a + 1\n" 400 in
    let once : String := fmt src in
    String.beq once want && String.beq (fmt once) once
