// Pins for `lang/src/elim_lower.mo` (`core-term-simplification.md` R3c): the
// one conversion from `Term.elim` back to `Literal.if_`/`Literal.match_`.
//
// Term-level on purpose -- the conversion is a pure representation change, so
// each pin hand-builds the `Elim` it names and inspects the produced shape.
// Scopes come from real parsed source (`try_parse_decls` + `build_scope_from_
// decls`), the same technique `proofs/src/checker/elim_props.mo` uses, so the
// resolved `Inductive` and constructor order are the real ones.
//
// Two parser traps are avoided deliberately: a constructor pattern nested
// inside another (`Term.lit (Literal.match_ _ cases)`) does not parse, and a
// `match` used as a match-ARM body is followed by another arm with no comma;
// hence the small accessors below, each with single-constructor patterns.

use std::list {List.length}
use lang::types {
    DebugName, Elim, Identifier, Inductive, Literal, MatchCase, ModulePath, NamePath, Scope,
    ScopeData, Similar, Term, binder_anon, binder_named, sentinel,
}
use lib::module {try_parse_decls}
use lib::scope {build_scope_from_decls, scope_find_inductive}
use lib::elim_lower {elim_to_literal}
use lib::typecheck::infer {canonicalize_ctor_refs}

def elim_lower_test_path : ModulePath := ModulePath.mk (List.cons (Identifier.id "elim_lower_tests") List.empty)

def scope_of (source : String) : Scope :=
    let sd : ScopeData :=
        match try_parse_decls source {
            Option.some decl_list => build_scope_from_decls elim_lower_test_path decl_list,
            Option.none => build_scope_from_decls elim_lower_test_path List.empty,
        } in
    {
        module_id := elim_lower_test_path,
        scope := sd,
        parent := Option.none,
        incomplete_match_ok := false,
    }

def named_var (name : String) : Term := Term.var sentinel (DebugName.named (Identifier.id name))

def one_field_minor : Term := Term.lam (binder_named (Identifier.id "r")) Term.hole (Term.var 0 DebugName.unnamed)

// ─── Shape accessors / predicates ──────────────────────────────────────

def match_cases_of (t : Term) : Option (List MatchCase) :=
    match t {
        Term.lit lit_ => match lit_ {
            Literal.match_ _ cases => Option.some cases,
            _ => Option.none,
        },
        _ => Option.none,
    }

def if_branches_of (t : Term) : Option (Pair Term Term) :=
    match t {
        Term.lit lit_ => match lit_ {
            Literal.if_ _ then_body else_body => Option.some (Pair.pair then_body else_body),
            _ => Option.none,
        },
        _ => Option.none,
    }

def first_two_cases (cases : List MatchCase) : Option (Pair MatchCase MatchCase) :=
    match cases {
        List.cons c1 rest => match rest {
            List.cons c2 _ => Option.some (Pair.pair c1 c2),
            _ => Option.none,
        },
        _ => Option.none,
    }

def first_case (cases : List MatchCase) : Option MatchCase :=
    match cases {
        List.cons c _ => Option.some c,
        _ => Option.none,
    }

def case_is_named (c : MatchCase) (want : String) : Bool :=
    match c {
        MatchCase.mk name _args _body _fp _typ_name => Similar.similar name (Identifier.id want),
    }

def case_first_arg_is (c : MatchCase) (want : String) : Bool :=
    match c {
        MatchCase.mk _name args _body _fp _typ_name =>
            match args {
                List.cons a _rest => Similar.similar a (Identifier.id want),
                List.empty => false,
            },
    }

def case_arg_count (c : MatchCase) : I64 :=
    match c {
        MatchCase.mk _name args _body _fp _typ_name => List.length args,
    }

def shape_pair_ok (c1 : MatchCase) (c2 : MatchCase) : Bool :=
    case_is_named c1 "circle"
        && case_is_named c2 "square"
        && case_first_arg_is c1 "r"
        && case_first_arg_is c2 "r"
        && I64.beq (case_arg_count c1) 1
        && I64.beq (case_arg_count c2) 1

// ─── Per-test bodies (kept out of match arms -- see the header) ─────────

def check_shape_cases (sc : Scope) (ind : Inductive) : Bool :=
    let m1 : Term := one_field_minor in
    let m2 : Term := one_field_minor in
    let e : Elim := Elim.mk ind.name List.empty List.empty List.empty Term.hole
        (List.cons m1 (List.cons m2 List.empty)) (Term.var 0 DebugName.unnamed) in
    match elim_to_literal sc e {
        Result.err _ => false,
        Result.ok result => match match_cases_of result {
            Option.none => false,
            Option.some cases => match first_two_cases cases {
                Option.none => false,
                Option.some pair => match pair {
                    Pair.pair c1 c2 => shape_pair_ok c1 c2,
                },
            },
        },
    }

def check_bool_branches (sc : Scope) (ind : Inductive) : Bool :=
    let false_body : Term := named_var "F" in
    let true_body : Term := named_var "T" in
    let e : Elim := Elim.mk ind.name List.empty List.empty List.empty Term.hole
        (List.cons false_body (List.cons true_body List.empty)) (Term.var 0 DebugName.unnamed) in
    match elim_to_literal sc e {
        Result.err _ => false,
        Result.ok result => match if_branches_of result {
            Option.none => false,
            Option.some pair => match pair {
                Pair.pair then_body else_body =>
                    Similar.similar then_body true_body && Similar.similar else_body false_body,
            },
        },
    }

def check_short_minor_rejected (sc : Scope) (ind : Inductive) : Bool :=
    let m1 : Term := named_var "not-a-lambda" in
    let m2 : Term := one_field_minor in
    let e : Elim := Elim.mk ind.name List.empty List.empty List.empty Term.hole
        (List.cons m1 (List.cons m2 List.empty)) (Term.var 0 DebugName.unnamed) in
    match elim_to_literal sc e {
        Result.err _ => true,
        Result.ok _ => false,
    }

def check_anonymous_binder (sc : Scope) (ind : Inductive) : Bool :=
    let m : Term := Term.lam binder_anon Term.hole Term.hole in
    let e : Elim := Elim.mk ind.name List.empty List.empty List.empty Term.hole
        (List.cons m List.empty) (Term.var 0 DebugName.unnamed) in
    match elim_to_literal sc e {
        Result.err _ => false,
        Result.ok result => match match_cases_of result {
            Option.none => false,
            Option.some cases => match first_case cases {
                Option.none => false,
                Option.some c => case_first_arg_is c "_",
            },
        },
    }

def check_unknown_inductive_rejected (sc : Scope) : Bool :=
    let bogus : NamePath := NamePath.mk (List.cons (Identifier.id "NoSuchInductive") List.empty) in
    let e : Elim := Elim.mk bogus List.empty List.empty List.empty Term.hole List.empty (Term.var 0 DebugName.unnamed) in
    match elim_to_literal sc e {
        Result.err _ => true,
        Result.ok _ => false,
    }

// ─── Pins ──────────────────────────────────────────────────────────────

/// A two-constructor, one-field-each inductive converts to a positional
/// `Literal.match_` case list in DECLARATION order, each case named after its
/// constructor and binding the minor's own binder name.
#[test]
def test_elim_to_literal_builds_match_cases_in_declaration_order : Bool :=
    let sc : Scope := scope_of "type Shape { circle (r : I64), square (r : I64) }" in
    match scope_find_inductive (NamePath.mk (List.cons (Identifier.id "Shape") List.empty)) sc {
        Result.err _ => false,
        Result.ok ind => check_shape_cases sc ind,
    }

/// `Literal.if_`'s then/else are chosen by constructor NAME, not position.
/// Here `Bool` is declared `false` then `true`, and the minors are supplied in
/// that declaration order, so a positional lowering would swap the branches.
#[test]
def test_elim_to_literal_bool_maps_branches_by_name : Bool :=
    let sc : Scope := scope_of "type Bool { false, true }" in
    match scope_find_inductive (NamePath.mk (List.cons (Identifier.id "Bool") List.empty)) sc {
        Result.err _ => false,
        Result.ok ind => check_bool_branches sc ind,
    }

/// A minor with fewer lambdas than its constructor has fields is a real arity
/// error, not something to silently realign (the checker never validates arm
/// arity, so this is the only place such a mismatch is caught).
#[test]
def test_elim_to_literal_rejects_a_short_minor : Bool :=
    let sc : Scope := scope_of "type Shape { circle (r : I64), square (r : I64) }" in
    match scope_find_inductive (NamePath.mk (List.cons (Identifier.id "Shape") List.empty)) sc {
        Result.err _ => false,
        Result.ok ind => check_short_minor_rejected sc ind,
    }

/// An unnamed binder becomes the corpus's `_` spelling.
#[test]
def test_elim_to_literal_names_an_anonymous_binder_underscore : Bool :=
    let sc : Scope := scope_of "type Box { box (v : I64) }" in
    match scope_find_inductive (NamePath.mk (List.cons (Identifier.id "Box") List.empty)) sc {
        Result.err _ => false,
        Result.ok ind => check_anonymous_binder sc ind,
    }

/// An `Elim` naming no registered inductive is refused, not lowered into a
/// case list nothing can dispatch.
#[test]
def test_elim_to_literal_rejects_an_unknown_inductive : Bool :=
    let sc : Scope := scope_of "type Shape { circle (r : I64) }" in
    check_unknown_inductive_rejected sc

/// A qualified constructor reference is canonicalized to the bare spelling a
/// derived motive uses (`Nat.succ` -> `succ`), including in a scope that keys
/// the owning inductive by its canonical path.
#[test]
def test_canonicalize_rewrites_a_qualified_constructor : Bool :=
    let sc : Scope := scope_of "type Nat { zero, succ (n : Nat) }" in
    let t : Term := Term.var sentinel (DebugName.named (Identifier.id "Nat.succ")) in
    let want : Term := Term.var sentinel (DebugName.named (Identifier.id "succ")) in
    Similar.similar (canonicalize_ctor_refs sc t) want
