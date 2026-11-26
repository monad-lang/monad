// Pins for `lang/src/elim_lower.mo`: a `Term.elim`'s minors as the
// per-constructor arms both backends compile.
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

use std::list {}
use lang::types {case_minors,
    DebugName, Elim, Identifier, Inductive, Literal, MatchCase, ModulePath, NamePath, Scope,
    ScopeData, Similar, Term, binder_anon, binder_named, sentinel,
}
use lib::module {try_parse_decls}
use lib::scope {build_scope_from_decls, scope_find_inductive}
use lib::elim_lower {ElimArm, bool_branches, elim_arms, elim_arms_in}
use lib::typecheck::infer {canonicalize_ctor_refs, empty_local_types, empty_locals, type_check}
use lib::typecheck::diagnostic {type_error_message}
use parsec::core {Text}

def elim_lower_test_path : ModulePath := ModulePath.mk (List.cons (Identifier.id "elim_lower_tests") List.empty)

def scope_of (source : String) : Scope :=
    let sd : ScopeData :=
        match try_parse_decls (Text.of_string source) {
            Option.some decl_list => build_scope_from_decls elim_lower_test_path decl_list,
            Option.none => build_scope_from_decls elim_lower_test_path List.empty,
        } in
    {
        module_id := elim_lower_test_path,
        scope := sd,
        parent := Option.none,
        elaboration_pass := false,
    }

def named_var (name : String) : Term := Term.var sentinel (DebugName.named (Identifier.id name))

def one_field_minor : Term := Term.lam (binder_named (Identifier.id "r")) Term.hole (Term.var 0 DebugName.unnamed)

// ─── Shape accessors / predicates ──────────────────────────────────────

def arms_of (sc : Scope) (e : Elim) : Option (List ElimArm) :=
    match elim_arms_in sc e {
        Result.ok found => match found { Pair.pair _ind arms => Option.some arms },
        Result.err _ => Option.none,
    }

def first_two_arms (arms : List ElimArm) : Option (Pair ElimArm ElimArm) :=
    match arms {
        List.cons a1 rest => match rest {
            List.cons a2 _ => Option.some (Pair.pair a1 a2),
            _ => Option.none,
        },
        _ => Option.none,
    }

def first_arm (arms : List ElimArm) : Option ElimArm :=
    match arms {
        List.cons a _ => Option.some a,
        _ => Option.none,
    }

def arm_is_named (a : ElimArm) (want : String) : Bool := Similar.similar a.ctor (Identifier.id want)

def arm_first_binder_is (a : ElimArm) (want : String) : Bool :=
    match a.binders {
        List.cons b _rest => Similar.similar b (Identifier.id want),
        List.empty => false,
    }

def shape_pair_ok (a1 : ElimArm) (a2 : ElimArm) : Bool :=
    arm_is_named a1 "circle"
        && arm_is_named a2 "square"
        && arm_first_binder_is a1 "r"
        && arm_first_binder_is a2 "r"
        && I64.beq (List.length a1.binders) 1
        && I64.beq (List.length a2.binders) 1

// ─── Per-test bodies (kept out of match arms -- see the header) ─────────

def check_shape_arms (sc : Scope) (ind : Inductive) : Bool :=
    let m1 : Term := one_field_minor in
    let m2 : Term := one_field_minor in
    let e : Elim := Elim.mk ind.name List.empty List.empty List.empty Term.hole
        (case_minors (List.cons m1 (List.cons m2 List.empty))) (Term.var 0 DebugName.unnamed) in
    match arms_of sc e {
        Option.none => false,
        Option.some arms => match first_two_arms arms {
            Option.none => false,
            Option.some pair => match pair {
                Pair.pair a1 a2 => shape_pair_ok a1 a2,
            },
        },
    }

def check_bool_branches (sc : Scope) (ind : Inductive) : Bool :=
    let false_body : Term := named_var "F" in
    let true_body : Term := named_var "T" in
    let e : Elim := Elim.mk ind.name List.empty List.empty List.empty Term.hole
        (case_minors (List.cons false_body (List.cons true_body List.empty))) (Term.var 0 DebugName.unnamed) in
    match arms_of sc e {
        Option.none => false,
        Option.some arms => match bool_branches ind arms {
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
        (case_minors (List.cons m1 (List.cons m2 List.empty))) (Term.var 0 DebugName.unnamed) in
    match elim_arms ind e {
        Result.err _ => true,
        Result.ok _ => false,
    }

def check_anonymous_binder (sc : Scope) (ind : Inductive) : Bool :=
    let m : Term := Term.lam binder_anon Term.hole Term.hole in
    let e : Elim := Elim.mk ind.name List.empty List.empty List.empty Term.hole
        (case_minors (List.cons m List.empty)) (Term.var 0 DebugName.unnamed) in
    match arms_of sc e {
        Option.none => false,
        Option.some arms => match first_arm arms {
            Option.none => false,
            Option.some a => arm_first_binder_is a "_",
        },
    }

def check_unknown_inductive_rejected (sc : Scope) : Bool :=
    let bogus : NamePath := NamePath.mk (List.cons (Identifier.id "NoSuchInductive") List.empty) in
    let e : Elim := Elim.mk bogus List.empty List.empty List.empty Term.hole List.empty (Term.var 0 DebugName.unnamed) in
    match elim_arms_in sc e {
        Result.err _ => true,
        Result.ok _ => false,
    }

// ─── Pins ──────────────────────────────────────────────────────────────

/// A two-constructor, one-field-each inductive gives one arm per constructor in
/// DECLARATION order, each named after its constructor and binding the minor's
/// own binder name.
#[test]
def test_elim_arms_are_in_declaration_order : Bool :=
    let sc : Scope := scope_of "type Shape { circle (r : I64), square (r : I64) }" in
    match scope_find_inductive (NamePath.mk (List.cons (Identifier.id "Shape") List.empty)) sc {
        Result.err _ => false,
        Result.ok ind => check_shape_arms sc ind,
    }

/// `bool_branches`' then/else are chosen by constructor NAME, not position.
/// Here `Bool` is declared `false` then `true`, and the minors are supplied in
/// that declaration order, so a positional lowering would swap the branches.
#[test]
def test_bool_branches_map_by_name : Bool :=
    let sc : Scope := scope_of "type Bool { false, true }" in
    match scope_find_inductive (NamePath.mk (List.cons (Identifier.id "Bool") List.empty)) sc {
        Result.err _ => false,
        Result.ok ind => check_bool_branches sc ind,
    }

/// A minor with fewer lambdas than its constructor has fields is a real arity
/// error, not something to silently realign (the checker never validates arm
/// arity, so this is the only place such a mismatch is caught).
#[test]
def test_elim_arms_reject_a_short_minor : Bool :=
    let sc : Scope := scope_of "type Shape { circle (r : I64), square (r : I64) }" in
    match scope_find_inductive (NamePath.mk (List.cons (Identifier.id "Shape") List.empty)) sc {
        Result.err _ => false,
        Result.ok ind => check_short_minor_rejected sc ind,
    }

/// An unnamed binder becomes the corpus's `_` spelling.
#[test]
def test_elim_arms_name_an_anonymous_binder_underscore : Bool :=
    let sc : Scope := scope_of "type Box { box (v : I64) }" in
    match scope_find_inductive (NamePath.mk (List.cons (Identifier.id "Box") List.empty)) sc {
        Result.err _ => false,
        Result.ok ind => check_anonymous_binder sc ind,
    }

/// An `Elim` naming no registered inductive is refused, not turned into arms
/// nothing can dispatch.
#[test]
def test_elim_arms_reject_an_unknown_inductive : Bool :=
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

// ─── Coverage on the elaboration pass (ISSUE-4) ────────────────────────

def tri_case (ctor : String) : MatchCase :=
    MatchCase.mk (Identifier.id ctor) List.empty (named_var "Tri.a") Option.none Option.none

/// The elaboration pass (`Scope.elaboration_pass`) has no coverage opt-out:
/// an incomplete match is rejected there too, so it never reaches a backend
/// as a match whose last arm catches the missing constructor's tag.
#[test]
def test_an_incomplete_match_is_rejected_on_the_elaboration_pass : Bool :=
    let sc : Scope := scope_of "type Tri { a, b, c }" in
    let elab : Scope := { sc with elaboration_pass := true } in
    let t : Term := Term.lit (Literal.match_ (named_var "Tri.a") [tri_case "a", tri_case "b"]) in
    match type_check t Term.hole elab empty_local_types empty_locals {
        Result.ok _ => false,
        Result.err e => String.contains (type_error_message e) "non-exhaustive match: `Tri.c`",
    }

/// The complete match on the same pass is an `Elim`, not a `Literal.match_`.
#[test]
def test_a_complete_match_is_an_elim_on_the_elaboration_pass : Bool :=
    let sc : Scope := scope_of "type Tri { a, b, c }" in
    let elab : Scope := { sc with elaboration_pass := true } in
    let t : Term := Term.lit (Literal.match_ (named_var "Tri.a") [tri_case "a", tri_case "b", tri_case "c"]) in
    match type_check t Term.hole elab empty_local_types empty_locals {
        Result.ok tt => is_elim tt.term,
        Result.err _ => false,
    }

def is_elim (t : Term) : Bool :=
    match t {
        Term.elim _ => true,
        Term.ctx _ inner => is_elim inner,
        _ => false,
    }
