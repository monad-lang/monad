/// Literal extraction from the HIR and the prefilter scans.
use regex::syntax::parser {parse, RxParsed}
use regex::hir {RxHir, RxFlags, translate}
use regex::literal {hir_literals, hir_first_bytes, hir_max_len, hir_dfa_ok, mask_has, literals_mask}
use regex::prefilter {scan_literals}
use std::list {List.all, List.intercalate}

def hir_of (pat : String) : Option RxHir :=
    let flags : RxFlags := {
        case_insensitive := false, multi_line := false, dot_matches_new_line := false,
        swap_greed := false, unicode := true,
    } in
    match parse pat false 250 {
        Result.ok parsed =>
            match translate parsed.ast flags {
                Result.ok h => Option.some h,
                Result.err _ => Option.none,
            },
        Result.err _ => Option.none,
    }

def render_lits (xs : List (List I64)) : String :=
    List.intercalate "|" (List.map (fn (l : List I64) => List.intercalate "," (List.map I64.to_string l)) xs)

/// The literal set as byte lists, or "-" when the pattern is not one.
def literal_set (pat : String) : String :=
    match hir_of pat {
        Option.some h =>
            match hir_literals h {
                Option.some ls => render_lits ls,
                Option.none => "-",
            },
        Option.none => "err",
    }

def max_len (pat : String) : I64 :=
    match hir_of pat {
        Option.some h =>
            match hir_max_len h {
                Option.some n => n,
                Option.none => 0 - 1,
            },
        Option.none => 0 - 2,
    }

/// Whether the first-byte set exists and holds exactly the `yes` bytes
/// among `probe`.
def first_has (pat : String) (yes : List I64) (no : List I64) : Bool :=
    match hir_of pat {
        Option.some h =>
            match hir_first_bytes h {
                Option.some m => List.all (fn (b : I64) => mask_has m b) yes && List.all (fn (b : I64) => Bool.not (mask_has m b)) no,
                Option.none => false,
            },
        Option.none => false,
    }

def no_first (pat : String) : Bool :=
    match hir_of pat {
        Option.some h =>
            match hir_first_bytes h {
                Option.some _ => false,
                Option.none => true,
            },
        Option.none => false,
    }

def dfa_ok (pat : String) : Bool :=
    match hir_of pat {
        Option.some h => hir_dfa_ok h,
        Option.none => false,
    }

#[test]
def test_literal_extraction : Bool :=
    String.beq (literal_set "abc") "97,98,99" && String.beq (literal_set "é") "195,169" && String.beq (literal_set "ab|c") "97,98|99"
        && String.beq (literal_set "a+") "-" && String.beq (literal_set "(a)") "-" && String.beq (literal_set "a|") "-"
        && String.beq (literal_set "^a") "-" && String.beq (literal_set "[ab]") "-" && String.beq (literal_set "") "-"

#[test]
def test_first_bytes : Bool :=
    first_has "abc" [97] [98, 99] && first_has "a*b" [97, 98] [99] && first_has "(x|yz)+" [120, 121] [122]
        && first_has "é" [195] [233] && first_has r#"^\d"# [48, 57] [97] && no_first "a*" && no_first "a|"

#[test]
def test_max_len : Bool :=
    I64.beq (max_len "abc") 3 && I64.beq (max_len "a{2,5}") 5 && I64.beq (max_len "a+") (0 - 1)
        && I64.beq (max_len "é|ab") 2 && I64.beq (max_len "日?") 3 && I64.beq (max_len "") 0

#[test]
def test_dfa_eligibility : Bool :=
    dfa_ok "^ab$" && dfa_ok r#"\Aa\z"# && Bool.not (dfa_ok r#"\b"#) && Bool.not (dfa_ok "(?m)^a")
        && Bool.not (dfa_ok r#"a\B"#)

def scan (ls : List (List I64)) (hay : String) : String :=
    match scan_literals ls (literals_mask ls) (String.to_list hay) 0 {
        Option.some sp => String.concat_list [I64.to_string sp.first, "-", I64.to_string sp.second],
        Option.none => "none",
    }

#[test]
def test_scan_literals : Bool :=
    String.beq (scan [[98, 99]] "abcbc") "1-3" && String.beq (scan [[97], [97, 98]] "xab") "1-2"
        && String.beq (scan [[97, 98], [97]] "xab") "1-3" && String.beq (scan [[122]] "abc") "none"
        && String.beq (scan [[97, 97, 98]] "aaaab") "2-5" && String.beq (scan [[99]] "") "none"
