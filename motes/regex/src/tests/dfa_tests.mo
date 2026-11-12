/// The lazy DFA and the meta strategy: every engine must report the spans
/// the Pike VM reports, and a cache too small to hold the DFA must give
/// up and fall back rather than grow (G3).
use regex::regex {
    Regex, Regex.new, Regex.find_all, Regex.captures_all, Regex.is_match, Regex.with_engine,
    Regex.new_cache, Regex.find_with, RegexBuilder, RegexBuilder.build, Match, Captures,
    Captures.get, Captures.len,
}
use regex::meta {RxEngine, RxStrategy, Cache, cache_gave_up, cache_clears}
use regex::nfa {RxProg, RxState, RxTrans}
use regex::table {table_get}
use std::array {Array}
use std::list {List.intercalate}

def bool_eq (a : Bool) (b : Bool) : Bool := if a then b else Bool.not b

def render (ms : List Match) : String :=
    List.intercalate " " (List.map (fn (m : Match) => String.concat_list [I64.to_string m.start, "-", I64.to_string m.end]) ms)

def group_span (c : Captures) (i : I64) : String :=
    match Captures.get c i {
        Option.some m => String.concat_list [I64.to_string m.start, "-", I64.to_string m.end],
        Option.none => "_",
    }

#[terminating]
def groups (c : Captures) (i : I64) (acc : List String) : List String :=
    if I64.lt i (Captures.len c) then groups c (i + 1) (List.cons (group_span c i) acc)
    else List.reverse acc

def render_caps (cs : List Captures) : String :=
    List.intercalate " " (List.map (fn (c : Captures) => List.intercalate "," (groups c 0 List.empty)) cs)

def strategy_name (r : Regex) : String :=
    match r.strategy {
        RxStrategy.strat_literal _ _ => "literal",
        RxStrategy.strat_dfa _ _ _ _ => "dfa",
        RxStrategy.strat_pike => "pike",
    }

def uses (pat : String) (want : String) : Bool :=
    match Regex.new pat {
        Result.ok r => String.beq (strategy_name r) want,
        Result.err _ => false,
    }

/// Spans and captures agree across the auto, bare-DFA and Pike engines,
/// and the spans are `want`.
def agree (pat : String) (hay : String) (want : String) : Bool :=
    match Regex.new pat {
        Result.ok r =>
            let auto : String := render (Regex.find_all r hay) in
            String.beq auto want
                && String.beq (render (Regex.find_all (Regex.with_engine r RxEngine.eng_pike) hay)) want
                && String.beq (render (Regex.find_all (Regex.with_engine r RxEngine.eng_dfa_bare) hay)) want
                && String.beq (render_caps (Regex.captures_all r hay))
                    (render_caps (Regex.captures_all (Regex.with_engine r RxEngine.eng_pike) hay))
                && bool_eq (Regex.is_match r hay) (Bool.not (String.beq want "")),
        Result.err _ => false,
    }

#[test]
def test_strategy_choice : Bool :=
    uses "abc" "literal" && uses "foo|bar" "literal" && uses "a+b" "dfa" && uses "(a)b" "dfa"
        && uses r#"\bx"# "pike" && uses "(?m)^a" "pike" && uses "^a$" "dfa" && uses "" "dfa"

#[test]
def test_priority : Bool :=
    agree "a|ab" "ab" "0-1" && agree "ab|a" "ab" "0-2" && agree "samwise|sam" "samwise sam" "0-7 8-11"
        && agree "a+?" "aaa" "0-1 1-2 2-3" && agree "a+" "aaa baa" "0-3 5-7" && agree "(a|ab)(c|bcd)" "abcd" "0-4"

#[test]
def test_empty_matches : Bool :=
    agree "a*" "baaa" "0-0 1-4" && agree "" "ab" "0-0 1-1 2-2" && agree "x*" "é" "0-0 2-2" && agree "a?" "" "0-0"

#[test]
def test_anchors : Bool :=
    agree "^a" "aa" "0-1" && agree "a$" "aa" "1-2" && agree "^a$" "a" "0-1" && agree "^$" "" "0-0"
        && agree "$" "ab" "2-2" && agree "a|$" "ba" "1-2" && agree r#"\Aab|b\z"# "abab" "0-2 3-4"

#[test]
def test_multibyte : Bool :=
    agree "é+" "caféé!" "3-7" && agree "[α-ω]+" "abc αβγ" "4-10" && agree r#"\w+"# "naïve 日本" "0-6 7-13"
        && agree "." "aé" "0-1 1-3"

#[test]
def test_captures_after_dfa : Bool :=
    agree r#"(\d{4})-(\d{2})"# "on 2026-11 and 1999-01" "3-10 15-22" && agree "(a)|(b)" "ab" "0-1 1-2"
        && agree "(a*)(b)?" "aab" "0-3"

#[test]
def test_prefilter_skips : Bool :=
    agree "xy+z" "aaaaaxyyzaaaxz xyz" "5-9 15-18" && agree "[xz]a" "bbbxbbza" "6-8"

/// A cache too small for even a few states: every new state clears it,
/// the search gives up after three clears, and the Pike VM answers.
#[test]
def test_tiny_cache_falls_back : Bool :=
    let pat : String := "(foo|bar|baz|qux)+[0-9]x" in
    let b : RegexBuilder := { pattern := pat, dfa_cache_limit := 200 } in
    match RegexBuilder.build b {
        Result.ok r =>
            let hay : String := "zzz foobar7x quxqux9x foo" in
            let warm : Pair (Option Match) Cache := Regex.find_with r (Regex.new_cache r) hay in
            String.beq (render (Regex.find_all r hay)) "4-12 13-21" && cache_gave_up warm.second
                && I64.lt 2 (cache_clears warm.second),
        Result.err _ => false,
    }

/// A warm cache gives the same answers and does not grow past its first
/// search's states on a repeat.
#[test]
def test_warm_cache : Bool :=
    match Regex.new "b+c" {
        Result.ok r =>
            let one : Pair (Option Match) Cache := Regex.find_with r (Regex.new_cache r) "abbbc" in
            let two : Pair (Option Match) Cache := Regex.find_with r one.second "xxbc" in
            (match two.first {
                Option.some m => I64.beq m.start 2 && I64.beq m.end 4,
                Option.none => false,
            })
                && Bool.not (cache_gave_up two.second),
        Result.err _ => false,
    }

// ─── Byte equivalence classes ───

/// A class boundary sits at each end of every byte range: no transition
/// tells apart two bytes of one class.
#[terminating]
def ranges_respect (classes : Array I64) (ranges : List (Pair I64 I64)) : Bool :=
    match ranges {
        List.empty => true,
        List.cons r rest =>
            (I64.beq r.first 0 || Bool.not (I64.beq (Array.get_or classes (r.first - 1) 0) (Array.get_or classes r.first 0)))
                && (I64.beq r.second 255 || Bool.not (I64.beq (Array.get_or classes r.second 0) (Array.get_or classes (r.second + 1) 0)))
                && ranges_respect classes rest,
    }

def state_ranges (st : RxState) : List (Pair I64 I64) :=
    match st {
        RxState.byte_range lo hi _ => [Pair.pair lo hi],
        RxState.sparse ts => List.map (fn (t : RxTrans) => Pair.pair t.lo t.hi) ts,
        _ => List.empty,
    }

#[terminating]
def classes_ok (p : RxProg) (i : I64) : Bool :=
    if I64.lt i p.len then ranges_respect p.classes (state_ranges (table_get p.states i RxState.dead)) && classes_ok p (i + 1)
    else true

def prog_classes_ok (pat : String) (most : I64) : Bool :=
    match Regex.new pat {
        Result.ok r => classes_ok r.prog 0 && I64.lt 0 r.prog.nclasses && I64.lt (r.prog.nclasses - 1) most,
        Result.err _ => false,
    }

#[test]
def test_byte_classes : Bool :=
    prog_classes_ok "a" 3 && prog_classes_ok "[a-z]+[0-9]" 5 && prog_classes_ok r#"\w+é"# 256
        && prog_classes_ok "(?s)." 256 && prog_classes_ok "" 1
