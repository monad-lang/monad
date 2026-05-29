use lang.types
open types
use lang.typecheck.unify

def run_unify (a : Term) (b : Term) : Bool :=
    result_is_ok (unify a b)

// --- Hole tests ---

@[test]
def test_unify_hole_left : Bool :=
    run_unify Term.hole (Term.type_ 1)

@[test]
def test_unify_hole_right : Bool :=
    run_unify (Term.type_ 1) Term.hole

@[test]
def test_unify_hole_hole : Bool :=
    run_unify Term.hole Term.hole

// --- Sort tests ---

@[test]
def test_unify_sort_same : Bool :=
    run_unify (Term.type_ 1) (Term.type_ 1)

@[test]
def test_unify_sort_cumulativity : Bool :=
    run_unify (Term.type_ 0) (Term.type_ 1)

@[test]
def test_unify_sort_too_small : Bool :=
    let ok : Bool := run_unify (Term.type_ 1) (Term.type_ 0) in
    Bool.not ok

// --- Pi tests ---

@[test]
def test_unify_pi_same : Bool :=
    let p1 : Term := Term.pi (Term.type_ 1) (Term.type_ 1) in
    let p2 : Term := Term.pi (Term.type_ 1) (Term.type_ 1) in
    run_unify p1 p2

@[test]
def test_unify_pi_arg_mismatch : Bool :=
    let p1 : Term := Term.pi (Term.type_ 2) (Term.type_ 1) in
    let p2 : Term := Term.pi (Term.type_ 0) (Term.type_ 1) in
    let ok : Bool := run_unify p1 p2 in
    Bool.not ok

@[test]
def test_unify_pi_ret_mismatch : Bool :=
    let p1 : Term := Term.pi (Term.type_ 1) (Term.type_ 2) in
    let p2 : Term := Term.pi (Term.type_ 1) (Term.type_ 0) in
    let ok : Bool := run_unify p1 p2 in
    Bool.not ok

@[test]
def test_unify_pi_vs_sort : Bool :=
    let p : Term := Term.pi (Term.type_ 1) (Term.type_ 1) in
    let ok : Bool := run_unify p (Term.type_ 1) in
    Bool.not ok

// --- Forall tests ---

@[test]
def test_unify_forall_stripped : Bool :=
    let body : Term := Term.type_ 1 in
    let f : Term := Term.forall (DebugName.named (Identifier.id "A")) (Term.type_ 1) body in
    run_unify f (Term.type_ 1)

@[test]
def test_unify_forall_both_sides : Bool :=
    let body_left : Term := Term.pi (Term.type_ 1) (Term.type_ 1) in
    let f_left : Term := Term.forall (DebugName.named (Identifier.id "A")) (Term.type_ 1) body_left in
    let body_right : Term := Term.pi (Term.type_ 1) (Term.type_ 1) in
    let f_right : Term := Term.forall (DebugName.named (Identifier.id "B")) (Term.type_ 1) body_right in
    run_unify f_left f_right

// --- Literal / structural mismatch ---

@[test]
def test_unify_lit_vs_type : Bool :=
    let lit : Term := Term.lit (Literal.str "hello") in
    let ok : Bool := run_unify lit (Term.type_ 1) in
    Bool.not ok

@[test]
def test_unify_var_vs_different_var : Bool :=
    let v1 : Term := Term.var 0 (DebugName.named (Identifier.id "x")) in
    let v2 : Term := Term.var 1 (DebugName.named (Identifier.id "y")) in
    let ok : Bool := run_unify v1 v2 in
    Bool.not ok

// --- Combined structures ---

@[test]
def test_unify_nested_pi : Bool :=
    let arg : Term := Term.type_ 1 in
    let inner_ret : Term := Term.type_ 1 in
    let outer_ret : Term := Term.pi arg inner_ret in
    let p1 : Term := Term.pi arg outer_ret in
    let p2 : Term := Term.pi arg outer_ret in
    run_unify p1 p2

// --- App tests (no deep structural matching for apps yet) ---

@[test]
def test_unify_app_same : Bool :=
    let f : Term := Term.var 0 (DebugName.unnamed) in
    let a : Term := Term.type_ 1 in
    let app1 : Term := Term.app f a in
    run_unify app1 app1

@[test]
def test_unify_app_different : Bool :=
    let app1 : Term := Term.app (Term.type_ 1) (Term.type_ 1) in
    let app2 : Term := Term.app (Term.type_ 0) (Term.type_ 1) in
    let ok : Bool := run_unify app1 app2 in
    Bool.not ok
