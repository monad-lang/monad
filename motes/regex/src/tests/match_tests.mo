/// End-to-end matching: `find_all` spans rendered as `s-e s-e ...`.
///
/// Cases marked `// upstream: <file> <name>` are ported from Rust's
/// `regex` crate testdata (MIT/Apache-2.0), with their expected spans.
use regex::regex {Regex, Regex.new, Regex.find_all, Regex.find, Regex.is_match, Match}
use regex::error {RegexError}
use std::list {List.intercalate}

def render (ms : List Match) : String :=
    List.intercalate " " (List.map (fn (m : Match) => String.concat_list [I64.to_string m.start, "-", I64.to_string m.end]) ms)

/// All matches of `pat` in `hay`, or `err: <message>`.
def spans (pat : String) (hay : String) : String :=
    match Regex.new pat {
        Result.ok r => render (Regex.find_all r hay),
        Result.err e => String.concat "err: " (RegexError.message e),
    }

def is (pat : String) (hay : String) (expected : String) : Bool := String.beq (spans pat hay) expected

// ─── Literals and concatenation ───

#[test]
def test_literals : Bool :=
    is "a" "a" "0-1"
        && is "abc" "xabcx" "1-4"
        && is "a" "aaa" "0-1 1-2 2-3"
        && is "ab" "xyz" ""
        && is "é" "café" "3-5"
        && is "日本" "こんにちは日本" "15-21"

// ─── Alternation and leftmost-first ───

#[test]
def test_leftmost_first : Bool :=
    is "a|ab" "ab" "0-1" // upstream: misc leftmost-first
        && is "ab|a" "ab" "0-2"
        && is "abc|b" "abc" "0-3"
        && is "samwise|sam" "samwise" "0-7"
        && is "sam|samwise" "samwise" "0-3"
        && is "foo|bar" "barfoo" "0-3 3-6"

// ─── Repetition ───

#[test]
def test_repetition : Bool :=
    is "a*" "aaa" "0-3"
        && is "a+" "baaab" "1-4"
        && is "a?" "a" "0-1"
        && is "a{2}" "aaaaa" "0-2 2-4"
        && is "a{2,3}" "aaaaa" "0-3 3-5"
        && is "a{2,}" "aaaaa" "0-5"
        && is "a{,2}" "aaa" "0-2 2-3"
        && is "(ab)+" "ababab" "0-6"

#[test]
def test_lazy : Bool :=
    is "a+?" "aaa" "0-1 1-2 2-3"
        && is "a*?" "aaa" "0-0 1-1 2-2 3-3"
        && is "a{2,3}?" "aaaaa" "0-2 2-4"
        && is "<.+?>" "<a><b>" "0-3 3-6"
        && is "<.+>" "<a><b>" "0-6"
        && is "(?U)a+" "aaa" "0-1 1-2 2-3"
        && is "(?U)a+?" "aaa" "0-3"

// ─── Empty matches (upstream: iter.toml) ───

#[test]
def test_empty_matches : Bool :=
    is "" "" "0-0" // upstream: iter empty-match
        && is "" "abc" "0-0 1-1 2-2 3-3"
        && is "a*" "baaa" "0-0 1-4"
        && is "a*" "aaab" "0-3 4-4"
        && is "" "é" "0-0 2-2" // never splits a scalar
        && is "x*" "日" "0-0 3-3"

// ─── Classes ───

#[test]
def test_classes : Bool :=
    is "[a-c]+" "xabcbx" "1-5"
        && is "[^a-c]+" "abxyzc" "2-5"
        && is "[[:digit:]]+" "ab123" "2-5"
        && is "[a-z&&[^aeiou]]+" "hello" "0-1 2-4"
        && is "[a-c--b]+" "abc" "0-1 2-3"
        && is "[a-c~~b-d]+" "abcd" "0-1 3-4"
        && is "." "a\nb" "0-1 2-3"
        && is "(?s)." "a\nb" "0-1 1-2 2-3"

#[test]
def test_perl_classes : Bool :=
    is r#"\d+"# "ab123c45" "2-5 6-8"
        && is r#"\d"# "٣" "0-2" // Arabic-Indic three: Unicode \d
        && is r#"\w+"# "héllo wörld" "0-6 7-13"
        && is r#"\s+"# "a \t\nb" "1-4"
        && is r#"\W+"# "ab, cd" "2-4"
        && is r#"(?-u:\w)+"# "aé" "0-1"

#[test]
def test_unicode_properties : Bool :=
    is r#"\p{Greek}+"# "abc αβγ def" "4-10"
        && is r#"\p{Lu}"# "aBcD" "1-2 3-4"
        && is r#"\pN+"# "x²3" "1-4"
        && is r#"\P{L}+"# "ab12cd" "2-4"
        && is r#"\p{sc=Cyrillic}+"# "жук" "0-6"
        && is r#"[\p{Greek}\d]+"# "α1β" "0-5"

// ─── Case insensitivity ───

#[test]
def test_case_insensitive : Bool :=
    is "(?i)abc" "xAbCx" "1-4"
        && is "(?i)k" "kK\u{212a}" "0-1 1-2 2-5" // KELVIN SIGN folds to k
        && is "(?i)[a-c]+" "ABCabc" "0-6"
        && is "(?i)σ" "Σσς" "0-2 2-4 4-6"
        && is "(?i-u)k" "kK\u{212a}" "0-1 1-2"
        && is "a(?i)b" "aB" "0-2"
        && is "(?i:a)b" "Ab AB" "0-2"

// ─── Anchors and boundaries ───

#[test]
def test_anchors : Bool :=
    is "^a" "aa" "0-1"
        && is "a$" "aa" "1-2"
        && is "^$" "" "0-0"
        && is "(?m)^a" "a\na" "0-1 2-3"
        && is "(?m)a$" "a\na" "0-1 2-3"
        && is "a$" "a\n" "" // `$` is end of text only without m
        && is r#"\Aa"# "aa" "0-1"
        && is r#"a\z"# "aa" "1-2"

#[test]
def test_word_boundaries : Bool :=
    is r#"\bfoo\b"# "foo foobar foo" "0-3 11-14"
        && is r#"\Bo\B"# "foo" "1-2"
        && is r#"\b"# "ab cd" "0-0 2-2 3-3 5-5"
        && is r#"\bé"# "é aé" "0-2"
        && is r#"(?-u:\b)x"# "éx x" "2-3 4-5"

// ─── Escapes ───

#[test]
def test_escapes : Bool :=
    is r#"\."# "a.b" "1-2"
        && is r#"\x41"# "BAB" "1-2"
        && is r#"\u{1F600}"# "a😀" "1-5"
        && is r#"a\ b"# "a b" "0-3"

#[test]
def test_verbose : Bool :=
    is "(?x) a b # comment\n c" "abc" "0-3"
        && is r#"(?x) a \  b"# "a b" "0-3"

// ─── Groups don't change spans ───

#[test]
def test_groups : Bool :=
    is "(a)(b)" "ab" "0-2"
        && is "(?:a|b)+" "abba" "0-4"
        && is "(?P<x>a)+" "aa" "0-2"
        && is "()" "a" "0-0 1-1"

#[test]
def test_is_match_and_find : Bool :=
    match Regex.new "b+" {
        Result.ok r =>
            Regex.is_match r "abbbc" && Bool.not (Regex.is_match r "ac")
                && (match Regex.find r "abbbc" {
                    Option.some m => String.beq (Match.as_str m) "bbb",
                    Option.none => false,
                }),
        Result.err _ => false,
    }

// ─── Errors surface from Regex.new ───

#[test]
def test_errors : Bool :=
    is "(a" "a" "err: unclosed group"
        && is r#"\p{Klingon}"# "a" "err: unrecognized Unicode class name"
        && is r#"(?-u)\pL"# "a" "err: Unicode classes are not allowed when the u flag is off"
