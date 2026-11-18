/// Fuzzy ranking: exact names first, then prefixes, then substrings, then
use std::list {List.any, List.filter}
/// scattered subsequences; externals only on request.

use lib::fuzzy {Fuzzy.Hit, Fuzzy.score, Fuzzy.search}
use lib::tests::support {fixture}

def score_or (q : String) (name : String) (path : String) : I64 :=
    match Fuzzy.score q name path { Option.some s => s, Option.none => 0 - 1 }

#[test]
def test_tiers_order : Bool :=
    let exact : I64 := score_or "unify" "unify" "lang::typecheck::unify::unify" in
    let prefix : I64 := score_or "unif" "unify_terms" "lang::typecheck::unify::unify_terms" in
    let inner : I64 := score_or "ify" "unify" "lang::typecheck::unify::unify" in
    let scattered : I64 := score_or "ufy" "unify" "lang::typecheck::unify::unify" in
    exact > prefix && prefix > inner && inner > scattered && scattered > 0

#[test]
def test_no_match_is_none : Bool :=
    match Fuzzy.score "zzz" "unify" "lang::typecheck::unify::unify" { Option.none => true, Option.some _ => false }

#[test]
def test_case_insensitive : Bool := score_or "list.map" "List.map" "std::list::List.map" == 1000

def first_key (hits : List Fuzzy.Hit) : String :=
    match hits { List.cons h _ => h.key, List.empty => "" }

#[test]
def test_search_ranks_exact_decl_first : Bool :=
    String.beq (first_key (Fuzzy.search fixture "whnf" 5 false)) "lang::typecheck::unify::whnf"

#[test]
def test_search_finds_modules_and_motes : Bool :=
    let hits : List Fuzzy.Hit := Fuzzy.search fixture "lang" 10 false in
    String.beq (first_key hits) "lang"
        && List.any (fn (h : Fuzzy.Hit) => String.beq h.level "module") hits

#[test]
def test_external_decls_only_on_request : Bool :=
    List.is_empty (List.filter (fn (h : Fuzzy.Hit) => String.beq h.level "decl")
        (Fuzzy.search fixture "List.map" 5 false))
        && String.beq (first_key (Fuzzy.search fixture "List.map" 5 true)) "std::list::List.map"

#[test]
def test_limit_bounds_results : Bool := List.length (Fuzzy.search fixture "e" 3 true) == 3
