use lib::types {
  LocalScope, ModulePath, Scope, Term, app, forall, hole, id, lit, named, pi,
  result_is_ok, sentinel, str, type_, unnamed, var,
}
use lib::typecheck::unify {unify}
use lib::scope {build_scope_from_decls}

/// An empty scope/locals pair. Every test below compares terms that
/// need no delta reduction, so there is nothing for `unify` to look up
/// -- conversion checking against a populated scope is exercised in
/// `whnf_tests.mo` and end-to-end in `typecheck_examples_tests.mo`.
def test_scope : Scope := {
    module_id := ModulePath.mp List.empty,
    scope := build_scope_from_decls (ModulePath.mp List.empty) List.empty,
    parent := Option.none,
}

def test_locals : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

def run_unify (a : Term) (b : Term) : Bool :=
    result_is_ok (unify a b test_scope test_locals)

// --- Hole tests ---

#[test]
def test_unify_hole_left : Bool :=
    run_unify Term.hole (Term.type_ 1)

#[test]
def test_unify_hole_right : Bool :=
    run_unify (Term.type_ 1) Term.hole

#[test]
def test_unify_hole_hole : Bool :=
    run_unify Term.hole Term.hole

// --- Sort tests ---

#[test]
def test_unify_sort_same : Bool :=
    run_unify (Term.type_ 1) (Term.type_ 1)

#[test]
def test_unify_sort_cumulativity : Bool :=
    run_unify (Term.type_ 0) (Term.type_ 1)

#[test]
def test_unify_sort_too_small : Bool :=
    let ok : Bool := run_unify (Term.type_ 1) (Term.type_ 0) in
    Bool.not ok

// --- Pi tests ---

#[test]
def test_unify_pi_same : Bool :=
    let p1 : Term := Term.pi (Term.type_ 1) (Term.type_ 1) in
    let p2 : Term := Term.pi (Term.type_ 1) (Term.type_ 1) in
    run_unify p1 p2

#[test]
def test_unify_pi_arg_mismatch : Bool :=
    let p1 : Term := Term.pi (Term.type_ 2) (Term.type_ 1) in
    let p2 : Term := Term.pi (Term.type_ 0) (Term.type_ 1) in
    let ok : Bool := run_unify p1 p2 in
    Bool.not ok

#[test]
def test_unify_pi_ret_mismatch : Bool :=
    let p1 : Term := Term.pi (Term.type_ 1) (Term.type_ 2) in
    let p2 : Term := Term.pi (Term.type_ 1) (Term.type_ 0) in
    let ok : Bool := run_unify p1 p2 in
    Bool.not ok

#[test]
def test_unify_pi_vs_sort : Bool :=
    let p : Term := Term.pi (Term.type_ 1) (Term.type_ 1) in
    let ok : Bool := run_unify p (Term.type_ 1) in
    Bool.not ok

// --- Forall tests ---

#[test]
def test_unify_forall_stripped : Bool :=
    let body : Term := Term.type_ 1 in
    let f : Term := Term.forall (DebugName.named (Identifier.id "A")) (Term.type_ 1) body in
    run_unify f (Term.type_ 1)

#[test]
def test_unify_forall_both_sides : Bool :=
    let body_left : Term := Term.pi (Term.type_ 1) (Term.type_ 1) in
    let f_left : Term := Term.forall (DebugName.named (Identifier.id "A")) (Term.type_ 1) body_left in
    let body_right : Term := Term.pi (Term.type_ 1) (Term.type_ 1) in
    let f_right : Term := Term.forall (DebugName.named (Identifier.id "B")) (Term.type_ 1) body_right in
    run_unify f_left f_right

// --- Literal / structural mismatch ---

#[test]
def test_unify_lit_vs_type : Bool :=
    let lit : Term := Term.lit (Literal.str "hello") in
    let ok : Bool := run_unify lit (Term.type_ 1) in
    Bool.not ok

#[test]
def test_unify_var_vs_different_var : Bool :=
    let v1 : Term := Term.var 0 (DebugName.named (Identifier.id "x")) in
    let v2 : Term := Term.var 1 (DebugName.named (Identifier.id "y")) in
    let ok : Bool := run_unify v1 v2 in
    Bool.not ok

// --- Combined structures ---

#[test]
def test_unify_nested_pi : Bool :=
    let arg : Term := Term.type_ 1 in
    let inner_ret : Term := Term.type_ 1 in
    let outer_ret : Term := Term.pi arg inner_ret in
    let p1 : Term := Term.pi arg outer_ret in
    let p2 : Term := Term.pi arg outer_ret in
    run_unify p1 p2

// --- App tests (no deep structural matching for apps yet) ---

#[test]
def test_unify_app_same : Bool :=
    let f : Term := Term.var 0 (DebugName.unnamed) in
    let a : Term := Term.type_ 1 in
    let app1 : Term := Term.app f a in
    run_unify app1 app1

#[test]
def test_unify_app_different : Bool :=
    let app1 : Term := Term.app (Term.type_ 1) (Term.type_ 1) in
    let app2 : Term := Term.app (Term.type_ 0) (Term.type_ 1) in
    let ok : Bool := run_unify app1 app2 in
    Bool.not ok

// --- conversion checking (definitional equality) ---
//
// `unify` compares structurally first and only reduces when that has
// already failed, so these are the cases that used to be reported as
// mismatches purely on spelling.

use lib::module {parse_all_decls}
use lib::parser::core {fail, success}

def conv_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "conv") List.empty)

/// `idt` is the identity on types, `konst` ignores its argument.
def conv_scope : Scope :=
    let src : String := "type P { p0 }\ndef idt (x : Type) : Type := x\ndef konst (x : Type) : Type := P" in
    {
        module_id := conv_path,
        scope :=
            match parse_all_decls src {
                success _ decl_list => build_scope_from_decls conv_path decl_list,
                fail _ => build_scope_from_decls conv_path List.empty,
            },
        parent := Option.none,
    }

def run_unify_conv (a : Term) (b : Term) : Bool :=
    result_is_ok (unify a b conv_scope test_locals)

def conv_free (nm : String) : Term := Term.var sentinel (DebugName.named (Identifier.id nm))

#[test]
def test_unify_reduces_application_to_match : Bool :=
    // `idt Prop` reduces to `Prop`; structurally they are an `app` and
    // a `type_`, which never matched before.
    run_unify_conv (Term.app (conv_free "idt") (Term.type_ 0)) (Term.type_ 0)

#[test]
def test_unify_reduces_application_on_either_side : Bool :=
    run_unify_conv (Term.type_ 0) (Term.app (conv_free "idt") (Term.type_ 0))

#[test]
def test_unify_reduces_both_sides : Bool :=
    // Two differently-spelled applications that reduce alike: `konst
    // Prop` discards its argument and yields `P`, and `idt P` yields
    // its argument, also `P`. Neither side is structurally anything
    // like the other.
    run_unify_conv (Term.app (conv_free "konst") (Term.type_ 0))
                   (Term.app (conv_free "idt") (conv_free "P"))

#[test]
def test_unify_still_rejects_when_reduction_disagrees : Bool :=
    // `idt Prop` reduces to `Prop` (sort 0), not `Type` (sort 1). The
    // retry must not turn every mismatch into a match.
    not (run_unify_conv (Term.app (conv_free "idt") (Term.type_ 1)) (Term.type_ 0))

#[test]
def test_unify_still_rejects_irreducible_mismatch : Bool :=
    // Neither side reduces at all -- the early-out path in
    // `unify_stuck`.
    not (run_unify_conv (conv_free "no_such_a") (conv_free "no_such_b"))
