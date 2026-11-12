/// Differential tests: seeded random patterns and haystacks over a small
/// alphabet, where every engine must agree with the Pike VM on the spans
/// of `find_all`, and the meta path with it on `captures_all`. The
/// engines: the auto strategy (literal scan, or the DFA with its
/// prefilter), the DFA without a prefilter, and the DFA under a cache so
/// small it gives up mid-search.
use regex::regex {
    Regex, Regex.new, Regex.find_all, Regex.captures_all, Regex.is_match, Regex.with_engine,
    RegexBuilder, RegexBuilder.build, Match, Captures, Captures.get, Captures.len,
}
use regex::meta {RxEngine}
use std::list {List.intercalate}
open IO {println}

/// A 31-bit LCG: the product stays below 2^62, so no I64 overflow.
def lcg (s : I64) : I64 := I64.and (s * 1103515245 + 12345) 2147483647

/// A value below `n` and the next seed.
def pick (s : I64) (n : I64) : Pair I64 I64 :=
    let s2 : I64 := lcg s in
    Pair.pair (I64.rem (I64.shr s2 8) n) s2

def atoms : List String := ["a", "b", "c", ".", "[ab]", "[^a]", "é", r#"\w"#, "[a-cé]"]

def nth (xs : List String) (i : I64) : String :=
    match List.get i xs {
        Option.some x => x,
        Option.none => "",
    }

/// A pattern of nesting `depth` and the next seed.
#[terminating]
def gen (s : I64) (depth : I64) : Pair String I64 :=
    let k : Pair I64 I64 := pick s (if I64.lt 0 depth then 10 else 1) in
    if I64.beq k.first 0 || I64.beq k.first 1 || I64.beq k.first 2 then gen_atom k.second
    else if I64.beq k.first 3 || I64.beq k.first 4 then gen_concat k.second (depth - 1)
    else if I64.beq k.first 5 then gen_alt k.second (depth - 1)
    else if I64.beq k.first 6 then gen_group k.second (depth - 1)
    else if I64.beq k.first 7 then gen_anchor k.second (depth - 1)
    else gen_rep k.second (depth - 1)

def gen_atom (s : I64) : Pair String I64 :=
    let k : Pair I64 I64 := pick s (List.length atoms) in
    Pair.pair (nth atoms k.first) k.second

#[terminating]
def gen_concat (s : I64) (depth : I64) : Pair String I64 :=
    let a : Pair String I64 := gen s depth in
    let b : Pair String I64 := gen a.second depth in
    Pair.pair (String.concat a.first b.first) b.second

#[terminating]
def gen_alt (s : I64) (depth : I64) : Pair String I64 :=
    let a : Pair String I64 := gen s depth in
    let b : Pair String I64 := gen a.second depth in
    Pair.pair (String.concat_list ["(?:", a.first, "|", b.first, ")"]) b.second

#[terminating]
def gen_group (s : I64) (depth : I64) : Pair String I64 :=
    let a : Pair String I64 := gen s depth in
    Pair.pair (String.concat_list ["(", a.first, ")"]) a.second

#[terminating]
def gen_anchor (s : I64) (depth : I64) : Pair String I64 :=
    let k : Pair I64 I64 := pick s 2 in
    let a : Pair String I64 := gen k.second depth in
    if I64.beq k.first 0 then Pair.pair (String.concat "^" a.first) a.second
    else Pair.pair (String.concat a.first "$") a.second

def reps : List String := ["*", "+", "?", "*?", "+?", "??", "{1,2}", "{2}", "{0,2}?"]

#[terminating]
def gen_rep (s : I64) (depth : I64) : Pair String I64 :=
    let a : Pair String I64 := gen s depth in
    let k : Pair I64 I64 := pick a.second (List.length reps) in
    Pair.pair (String.concat_list ["(?:", a.first, ")", nth reps k.first]) k.second

def hay_units : List String := ["a", "b", "c", "é", "ab", "x"]

#[terminating]
def gen_hay (s : I64) (n : I64) (acc : List String) : Pair String I64 :=
    if I64.lt 0 n then
        let k : Pair I64 I64 := pick s (List.length hay_units) in
        gen_hay k.second (n - 1) (List.cons (nth hay_units k.first) acc)
    else Pair.pair (String.concat_list acc) s

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

/// "" when every engine agrees on `hay`, else a description.
def compare (r : Regex) (tiny : Regex) (pat : String) (hay : String) : String :=
    let want : String := render (Regex.find_all (Regex.with_engine r RxEngine.eng_pike) hay) in
    let auto : String := render (Regex.find_all r hay) in
    let bare : String := render (Regex.find_all (Regex.with_engine r RxEngine.eng_dfa_bare) hay) in
    let small : String := render (Regex.find_all tiny hay) in
    let caps_ok : Bool :=
        String.beq (render_caps (Regex.captures_all r hay)) (render_caps (Regex.captures_all (Regex.with_engine r RxEngine.eng_pike) hay)) in
    let is_ok : Bool := bool_eq (Regex.is_match r hay) (Bool.not (List.is_empty (Regex.find_all (Regex.with_engine r RxEngine.eng_pike) hay))) in
    if String.beq want auto && String.beq want bare && String.beq want small && caps_ok && is_ok then ""
    else
        String.concat_list [
            "pattern ", pat, " on \"", hay, "\": pike [", want, "] auto [", auto, "] bare [", bare,
            "] tiny [", small, "] captures ", (if caps_ok then "ok" else "differ"), " is_match ",
            (if is_ok then "ok" else "differ"),
        ]

/// Up to `n` patterns, each against `per` haystacks; the failures found.
#[terminating]
def run (s : I64) (n : I64) (per : I64) (acc : List String) : List String :=
    if I64.lt 0 n then
        let p : Pair String I64 := gen s 4 in
        let b : RegexBuilder := { pattern := p.first, dfa_cache_limit := 300 } in
        match Regex.new p.first {
            Result.ok r =>
                match RegexBuilder.build b {
                    Result.ok tiny => run_hays r tiny p.first p.second n per per acc,
                    Result.err _ => run p.second (n - 1) per (List.cons (String.concat "tiny build failed: " p.first) acc),
                },
            Result.err _ => run p.second (n - 1) per (List.cons (String.concat "build failed: " p.first) acc),
        }
    else acc

#[terminating]
def run_hays (r : Regex) (tiny : Regex) (pat : String) (s : I64) (n : I64) (per : I64) (k : I64) (acc : List String) : List String :=
    if I64.lt 0 k then
        let len : Pair I64 I64 := pick s 9 in
        let h : Pair String I64 := gen_hay len.second len.first List.empty in
        let res : String := compare r tiny pat h.first in
        run_hays r tiny pat h.second n per (k - 1) (if String.beq res "" then acc else List.cons res acc)
    else run s (n - 1) per acc

#[terminating]
def print_all (xs : List String) : IO Unit :=
    match xs {
        List.empty => IO.pure Unit.unit,
        List.cons x rest => do {
            println x;
            print_all rest
        },
    }

def check_seed (seed : I64) : IO Bool := do {
    let failures := List.reverse (run seed 150 6 List.empty);
    print_all failures;
    return (List.is_empty failures)
}

#[test]
def test_differential_seed_1 : IO Bool := check_seed 1

#[test]
def test_differential_seed_2 : IO Bool := check_seed 20261112

#[test]
def test_differential_seed_3 : IO Bool := check_seed 777
