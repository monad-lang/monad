/// The public API beyond spans: captures, replacement, splitting,
/// escaping and the builder.
use regex::regex {
    Regex, Regex.new, Regex.find, Regex.find_at, Regex.captures, Regex.captures_all,
    Regex.replace, Regex.replace_all, Regex.replace_all_with, Regex.split, Regex.splitn,
    Regex.escape, Regex.as_str, Regex.captures_len, Regex.is_match, RegexBuilder,
    RegexBuilder.build, Match, Captures, Captures.get, Captures.name, Captures.len,
}
use regex::error {RegexError}
use std::list {List.intercalate}

def with_re (pat : String) (f : Regex -> Bool) : Bool :=
    match Regex.new pat {
        Result.ok r => f r,
        Result.err _ => false,
    }

def group_is (c : Captures) (i : I64) (want : String) : Bool :=
    match Captures.get c i {
        Option.some m => String.beq (Match.as_str m) want,
        Option.none => false,
    }

def name_is (c : Captures) (n : String) (want : String) : Bool :=
    match Captures.name c n {
        Option.some m => String.beq (Match.as_str m) want,
        Option.none => false,
    }

def joined (xs : List String) : String := List.intercalate "|" xs

/// The plan's usage example.
#[test]
def test_find_date : Bool :=
    with_re r#"(?<y>\d{4})-(?<m>\d{2})-(?<d>\d{2})"# (fn (re : Regex) =>
        match Regex.find re "released 2026-11-07" {
            Option.some m => String.beq (Match.as_str m) "2026-11-07",
            Option.none => false,
        })

#[test]
def test_captures : Bool :=
    with_re r#"(?<y>\d{4})-(?<m>\d{2})-(?<d>\d{2})"# (fn (re : Regex) =>
        match Regex.captures re "on 2026-11-07." {
            Option.some c =>
                group_is c 0 "2026-11-07" && group_is c 1 "2026" && name_is c "m" "11"
                    && name_is c "d" "07" && I64.beq (Captures.len c) 4,
            Option.none => false,
        })

#[test]
def test_unmatched_group_is_none : Bool :=
    with_re "(a)|(b)" (fn (re : Regex) =>
        match Regex.captures re "b" {
            Option.some c =>
                (match Captures.get c 1 { Option.some _ => false, Option.none => true })
                    && group_is c 2 "b",
            Option.none => false,
        })

/// Captures follow leftmost-first priority, not longest.
#[test]
def test_capture_priority : Bool :=
    with_re "(a*)(a*)" (fn (re : Regex) =>
        match Regex.captures re "aaa" {
            Option.some c => group_is c 1 "aaa" && group_is c 2 "",
            Option.none => false,
        })
        && with_re "(a*?)(a*)" (fn (re : Regex) =>
            match Regex.captures re "aaa" {
                Option.some c => group_is c 1 "" && group_is c 2 "aaa",
                Option.none => false,
            })
        && with_re "(a|ab)(c|bcd)" (fn (re : Regex) =>
            match Regex.captures re "abcd" {
                Option.some c => group_is c 0 "abcd" && group_is c 1 "a" && group_is c 2 "bcd",
                Option.none => false,
            })

/// The last iteration of a repeated group wins.
#[test]
def test_repeated_group_capture : Bool :=
    with_re "(?:(a)|(b))+" (fn (re : Regex) =>
        match Regex.captures re "ab" {
            Option.some c => group_is c 2 "b" && group_is c 1 "a",
            Option.none => false,
        })

#[test]
def test_captures_all : Bool :=
    with_re r#"(\w)(\d)"# (fn (re : Regex) =>
        String.beq (joined (List.map (fn (c : Captures) => match Captures.get c 2 {
            Option.some m => Match.as_str m,
            Option.none => "?",
        }) (Regex.captures_all re "a1 b2 c3"))) "1|2|3")

#[test]
def test_find_at_keeps_context : Bool :=
    with_re r#"\bb"# (fn (re : Regex) =>
        (match Regex.find_at re "ab b" 1 {
            Option.some m => I64.beq m.start 3,
            Option.none => false,
        }))
        && with_re "^a" (fn (re : Regex) =>
            match Regex.find_at re "aa" 1 {
                Option.some _ => false,
                Option.none => true,
            })

#[test]
def test_replace : Bool :=
    with_re r#"(\w+) (\w+)"# (fn (re : Regex) => String.beq (Regex.replace re "hello world" "$2 $1") "world hello")
        && with_re r#"(?<first>\w+) (?<last>\w+)"# (fn (re : Regex) =>
            String.beq (Regex.replace re "Jane Doe" "${last}, ${first}") "Doe, Jane")
        && with_re "a" (fn (re : Regex) => String.beq (Regex.replace re "banana" "o") "bonana")
        && with_re "a" (fn (re : Regex) => String.beq (Regex.replace_all re "banana" "o") "bonono")
        && with_re "x" (fn (re : Regex) => String.beq (Regex.replace_all re "banana" "o") "banana")
        && with_re r#"(\d)"# (fn (re : Regex) => String.beq (Regex.replace_all re "a1b2" "<$1>") "a<1>b<2>")
        && with_re "a" (fn (re : Regex) => String.beq (Regex.replace_all re "a" "$$") "$")
        && with_re "a" (fn (re : Regex) => String.beq (Regex.replace_all re "a" "${9}|$nope|$") "||$")
        && with_re r#"(\d)"# (fn (re : Regex) => String.beq (Regex.replace_all re "1" "$1a") "")
        && with_re "" (fn (re : Regex) => String.beq (Regex.replace_all re "ab" "-") "-a-b-")

#[test]
def test_replace_all_with : Bool :=
    with_re r#"\d+"# (fn (re : Regex) =>
        String.beq (Regex.replace_all_with re "a1b22" (fn (c : Captures) => match Captures.get c 0 {
            Option.some m => I64.to_string (Match.len m),
            Option.none => "",
        })) "a1b2")

#[test]
def test_split : Bool :=
    with_re "," (fn (re : Regex) => String.beq (joined (Regex.split re "a,b,,c")) "a|b||c")
        && with_re "," (fn (re : Regex) => String.beq (joined (Regex.split re "a,b,")) "a|b|")
        && with_re r#"\s+"# (fn (re : Regex) => String.beq (joined (Regex.split re "a  b\tc")) "a|b|c")
        && with_re "" (fn (re : Regex) => String.beq (joined (Regex.split re "abc")) "|a|b|c|")
        && with_re "x" (fn (re : Regex) => String.beq (joined (Regex.split re "")) "")
        && with_re "," (fn (re : Regex) => String.beq (joined (Regex.splitn re "a,b,c" 2)) "a|b,c")
        && with_re "," (fn (re : Regex) => I64.beq (List.length (Regex.splitn re "a,b,c" 0)) 0)
        && with_re "," (fn (re : Regex) => String.beq (joined (Regex.splitn re "a,b,c" 5)) "a|b|c")

#[test]
def test_escape : Bool :=
    String.beq (Regex.escape "a.b*c") r#"a\.b\*c"#
        && with_re (Regex.escape "1+1=2?") (fn (re : Regex) => Regex.is_match re "is 1+1=2?")

#[test]
def test_builder : Bool :=
    let b : RegexBuilder := { pattern := "ABC", case_insensitive := true } in
    (match RegexBuilder.build b {
        Result.ok re => Regex.is_match re "xabcx" && String.beq (Regex.as_str re) "ABC",
        Result.err _ => false,
    })
        && (let m : RegexBuilder := { pattern := "^b", multi_line := true } in
            match RegexBuilder.build m {
                Result.ok re => Regex.is_match re "a\nb",
                Result.err _ => false,
            })
        && (let x : RegexBuilder := { pattern := "a b", ignore_whitespace := true } in
            match RegexBuilder.build x {
                Result.ok re => Regex.is_match re "ab",
                Result.err _ => false,
            })
        && with_re "(a)(b)" (fn (re : Regex) => I64.beq (Regex.captures_len re) 3)

/// G2: a program over the size limit is refused before it is built.
#[test]
def test_size_limit : Bool :=
    (match Regex.new "(a{100}){100}{100}" {
        Result.err e => String.beq (RegexError.message e) "compiled regex exceeds the size limit of 10485760",
        Result.ok _ => false,
    })
        && (let small : RegexBuilder := { pattern := r#"\w{50}"#, size_limit := 1000 } in
            match RegexBuilder.build small {
                Result.err _ => true,
                Result.ok _ => false,
            })

/// `is_match` stops at the first accept but agrees with `find`.
#[test]
def test_is_match_earliest : Bool :=
    with_re "a+|b" (fn (re : Regex) => Regex.is_match re "xaaaa" && Bool.not (Regex.is_match re "xyz"))
        && with_re r#"\bfoo$"# (fn (re : Regex) => Regex.is_match re "a foo" && Bool.not (Regex.is_match re "afoo"))
