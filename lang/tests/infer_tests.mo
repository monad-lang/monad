use lang.types
open types
use lang.scope
open scope
use lang.typecheck.infer

open Term
open DebugName
open Identifier
open ModulePath
open Multiplicity
open Literal
open NumSuffix
open TypeError

// --- Test scope setup: empty decls with builtins (Type, Prop) ---

def empty_path : ModulePath := ModulePath.mp List.empty
def empty_decls : List Decl := List.empty
def test_sd : ScopeData := build_scope_from_decls empty_path empty_decls
def test_scope : Scope := {
    module_id := empty_path,
    scope := test_sd,
    parent := Option.none,
}

def run_check (t : Term) (e : Term) : Result TypeError TypedTerm :=
    type_check t e test_scope empty_local_types empty_locals

// --- Sort / universe tests ---

@[test]
def test_sort_prop_is_type : Bool :=
    match run_check (Term.type_ 0) (Term.type_ 1) {
        ok _ => true,
        err _ => false,
    }

@[test]
def test_sort_type_is_type1 : Bool :=
    match run_check (Term.type_ 1) (Term.type_ 2) {
        ok _ => true,
        err _ => false,
    }

@[test]
def test_sort_cumulativity_prop_in_type : Bool :=
    match run_check (Term.type_ 0) (Term.type_ 2) {
        ok _ => true,
        err _ => false,
    }

@[test]
def test_sort_cumulativity_type_in_type2 : Bool :=
    match run_check (Term.type_ 1) (Term.type_ 3) {
        ok _ => true,
        err _ => false,
    }

@[test]
def test_sort_reject_too_small : Bool :=
    match run_check (Term.type_ 2) (Term.type_ 1) {
        ok _ => false,
        err e => match e {
            not_a_type _ => true,
            _ => false,
        },
    }

@[test]
def test_sort_infer_prop : Bool :=
    match run_check (Term.type_ 0) Term.hole {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (Term.type_ 1) },
        err _ => false,
    }

@[test]
def test_sort_infer_type : Bool :=
    match run_check (Term.type_ 1) Term.hole {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (Term.type_ 2) },
        err _ => false,
    }

// --- Variable tests ---

@[test]
def test_var_bound_simple : Bool :=
    let dbg : DebugName := DebugName.unnamed in
    let types : List Term := List.cons (Term.type_ 1) List.empty in
    match type_check (Term.var 0 dbg) Term.hole test_scope types empty_locals {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (Term.type_ 1) },
        err _ => false,
    }

@[test]
def test_var_bound_oob : Bool :=
    let dbg : DebugName := DebugName.unnamed in
    match type_check (Term.var 0 dbg) Term.hole test_scope empty_local_types empty_locals {
        ok _ => false,
        err e => match e {
            unknown_var _ => true,
            _ => false,
        },
    }

@[test]
def test_var_free_unnamed : Bool :=
    let dbg : DebugName := DebugName.unnamed in
    match run_check (Term.var sentinel dbg) Term.hole {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (Term.type_ 1) },
        err _ => false,
    }

@[test]
def test_var_free_unknown : Bool :=
    let id : Identifier := Identifier.id "no_such_var" in
    let dbg : DebugName := DebugName.named id in
    match run_check (Term.var sentinel dbg) Term.hole {
        ok _ => false,
        err e => match e {
            unknown_var _ => true,
            _ => false,
        },
    }

// --- Pi tests ---

@[test]
def test_pi_simple : Bool :=
    let t : Term := Term.pi (Term.type_ 1) (Term.type_ 1) in
    match run_check t Term.hole {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (Term.type_ 1) },
        err _ => false,
    }

@[test]
def test_pi_dependent : Bool :=
    let dbg : DebugName := DebugName.named (Identifier.id "A") in
    let arg : Term := Term.type_ 1 in
    let ret : Term := Term.var 0 dbg in
    let t : Term := Term.pi arg ret in
    let types : List Term := List.cons arg List.empty in
    match type_check t Term.hole test_scope types empty_locals {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (Term.type_ 1) },
        err _ => false,
    }

@[test]
def test_pi_arg_is_not_type : Bool :=
    let id : Identifier := Identifier.id "x" in
    let dbg : DebugName := DebugName.named id in
    let var_term : Term := Term.var sentinel dbg in
    let t : Term := Term.pi var_term (Term.type_ 1) in
    match run_check t Term.hole {
        ok _ => false,
        err _ => true,
    }

// --- Lambda tests ---

@[test]
def test_lam_check_mode : Bool :=
    let dbg : DebugName := DebugName.named (Identifier.id "x") in
    let body : Term := Term.var 0 dbg in
    let arg_typ : Term := Term.type_ 1 in
    let expected : Term := Term.pi arg_typ arg_typ in
    let lam : Term := Term.lam dbg arg_typ body in
    match run_check lam expected {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ expected },
        err _ => false,
    }

@[test]
def test_lam_infer_mode : Bool :=
    let dbg : DebugName := DebugName.named (Identifier.id "x") in
    let body : Term := Term.var 0 dbg in
    let arg_typ : Term := Term.type_ 1 in
    let lam : Term := Term.lam dbg arg_typ body in
    match run_check lam Term.hole {
        ok tt =>
            match tt { mk _ typ =>
                match typ {
                    pi a _ => Similar.similar a arg_typ,
                    _ => false,
                }},
        err _ => false,
    }

@[test]
def test_lam_unnamed : Bool :=
    let dbg : DebugName := DebugName.unnamed in
    let body : Term := Term.var 0 dbg in
    let arg_typ : Term := Term.type_ 1 in
    let expected : Term := Term.pi arg_typ arg_typ in
    let lam : Term := Term.lam dbg arg_typ body in
    match run_check lam expected {
        ok _ => true,
        err _ => false,
    }

// --- Application tests ---

@[test]
def test_app_id : Bool :=
    let x_dbg : DebugName := DebugName.named (Identifier.id "x") in
    let arg_typ : Term := Term.type_ 1 in
    let id_body : Term := Term.var 0 x_dbg in
    let id_lam : Term := Term.lam x_dbg arg_typ id_body in
    let result : Term := Term.app id_lam (Term.type_ 1) in
    match run_check result Term.hole {
        ok _ => true,
        err _ => false,
    }

@[test]
def test_app_with_hole_return : Bool :=
    let x_dbg : DebugName := DebugName.named (Identifier.id "x") in
    let arg_typ : Term := Term.type_ 1 in
    let id_body : Term := Term.var 0 x_dbg in
    let id_lam : Term := Term.lam x_dbg arg_typ id_body in
    let result : Term := Term.app id_lam (Term.type_ 0) in
    match run_check result Term.hole {
        ok _ => true,
        err _ => false,
    }

// --- Forall tests ---

@[test]
def test_forall_infer : Bool :=
    let a_dbg : DebugName := DebugName.named (Identifier.id "A") in
    let kind : Term := Term.type_ 1 in
    let body : Term := Term.type_ 1 in
    let t : Term := Term.forall a_dbg kind body in
    match run_check t Term.hole {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (Term.type_ 1) },
        err _ => false,
    }

@[test]
def test_forall_unnamed : Bool :=
    let dbg : DebugName := DebugName.unnamed in
    let kind : Term := Term.type_ 1 in
    let body : Term := Term.type_ 1 in
    let t : Term := Term.forall dbg kind body in
    match run_check t Term.hole {
        ok _ => true,
        err _ => false,
    }

// --- If tests ---

@[test]
def test_if_simple : Bool :=
    let cond : Term := Term.var 0 (DebugName.unnamed) in
    let then_ : Term := Term.type_ 1 in
    let else_ : Term := Term.type_ 1 in
    let if_t : Term := Term.lit (Literal.if_ cond then_ else_) in
    let bool_typ : Term := Term.type_ 1 in
    let types : List Term := List.cons bool_typ List.empty in
    match type_check if_t Term.hole test_scope types empty_locals {
        ok _ => true,
        err _ => false,
    }

// --- Match tests (basic structure) ---

@[test]
def test_match_empty_cases : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let t : Term := Term.lit (Literal.match_ scrutinee List.empty) in
    match run_check t Term.hole {
        ok _ => true,
        err _ => false,
    }

@[test]
def test_match_single_case : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let body : Term := Term.type_ 1 in
    let case_ : MatchCase := MatchCase.mc (Identifier.id "x") List.empty body in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match run_check t Term.hole {
        ok _ => true,
        err _ => false,
    }

// --- Match tests: multi-case processing ---

// BUG: type_check_cases only processes the head case and drops the rest.
// Two cases with both valid bodies: the match succeeds (but rest is ignored).
@[test]
def test_match_multi_case_bodies_ok : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let body1 : Term := Term.type_ 1 in
    let body2 : Term := Term.type_ 1 in
    let case1 : MatchCase := MatchCase.mc (Identifier.id "a") List.empty body1 in
    let case2 : MatchCase := MatchCase.mc (Identifier.id "b") List.empty body2 in
    let cases : List MatchCase := List.cons case1 (List.cons case2 List.empty) in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match run_check t Term.hole {
        ok _ => true,
        err _ => false,
    }

// KNOWN BUG: type_check_cases only processes the head case and drops the rest.
// The second case body has a type error but is never checked.
// FIX: When the case list has more than one element, check all cases and
// return the type from the first case's body.
@[test]
def test_match_multi_case_second_fails_known_bug : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let body1 : Term := Term.type_ 1 in
    let bad_var : Term := Term.var sentinel (DebugName.named (Identifier.id "no_such")) in
    let case1 : MatchCase := MatchCase.mc (Identifier.id "a") List.empty body1 in
    let case2 : MatchCase := MatchCase.mc (Identifier.id "b") List.empty bad_var in
    let cases : List MatchCase := List.cons case1 (List.cons case2 List.empty) in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match run_check t Term.hole {
        ok _ => true,    // BUG: succeeds when it should fail (second case not checked)
        err _ => false,  // CORRECT: would be err _ => true after fix
    }

// --- Match tests: constructor pattern args ---

// KNOWN BUG: Constructor pattern args are not added to the local scope or
// local_types, so the case body cannot reference them. The body references
// "x" which should be bound by the pattern.
// FIX: After matching a constructor, add its params to local_types and locals
// before type-checking the case body (substituting the inductive's type params).
@[test]
def test_match_case_args_not_bound_known_bug : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let arg_id : Identifier := Identifier.id "x" in
    let body : Term := Term.var sentinel (DebugName.named arg_id) in
    let case_ : MatchCase := MatchCase.mc
        (Identifier.id "some")
        (List.cons arg_id List.empty)
        body in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match run_check t Term.hole {
        ok _ => false,  // CORRECT: would be ok _ => true after fix
        err _ => true,  // BUG: fails because "x" is not in scope
    }

// --- Match tests: constructor validation with inductive ---

// Build a scope containing a simple Maybe-like inductive.
// Maybe has constructors: some (with one field), none (no fields).
def maybe_scope : Scope :=
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let type_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Maybe") List.empty) in
    let some_cn : InductConstructor := InductConstructor.mk
        (ModulePath.mp (List.cons (Identifier.id "some") List.empty))
        List.empty
        (Term.type_ 1) in
    let none_cn : InductConstructor := InductConstructor.mk
        (ModulePath.mp (List.cons (Identifier.id "none") List.empty))
        List.empty
        (Term.type_ 1) in
    let cns : List InductConstructor := List.cons some_cn (List.cons none_cn List.empty) in
    let empty_params : List Param := List.empty in
    let empty_attrs : List String := List.empty in
    let ind : Inductive := Inductive.mk
        type_name empty_params (Term.type_ 1) cns empty_attrs in
    let decls : List Decl := List.cons (Decl.inductive_d ind) List.empty in
    let sd : ScopeData := build_scope_from_decls mod_path decls in
    {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    }

@[test]
def test_match_inductive_in_scope : Bool :=
    match scope_find_inductive (ModulePath.mp (List.cons (Identifier.id "Maybe") List.empty)) maybe_scope {
        ok _ => true,
        err _ => false,
    }

// Match on a scrutinee with a valid constructor name. Constructor validation
// (looking up the constructor in the inductive) is not yet implemented, so
// this passes by default without verifying the constructor exists.
@[test]
def test_match_valid_constructor : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let body : Term := Term.type_ 1 in
    let case_ : MatchCase := MatchCase.mc
        (Identifier.id "some")
        List.empty
        body in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match type_check t Term.hole maybe_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

// KNOWN BUG: Constructor names on match cases are not validated against the
// scrutinee's inductive type. The name "bogus" should be rejected because it
// is not a constructor of Maybe.
// FIX: After inferring the scrutinee type, extract its inductive name, look
// it up in scope, and verify that each case's constructor name exists in the
// inductive's constructors list.
@[test]
def test_match_invalid_constructor_known_bug : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let body : Term := Term.type_ 1 in
    let case_ : MatchCase := MatchCase.mc
        (Identifier.id "bogus")
        List.empty
        body in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match type_check t Term.hole maybe_scope empty_local_types empty_locals {
        ok _ => true,    // BUG: succeeds when it should fail (constructor not validated)
        err _ => false,   // CORRECT: would be err _ => true after fix
    }

// --- Match tests: wildcard pattern ---

// Wildcard case (name "_") with no args.
// BUG: Wildcard handling (args verification, branch type accumulation)
// is not yet implemented.
@[test]
def test_match_wildcard : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let body : Term := Term.type_ 1 in
    let case_ : MatchCase := MatchCase.mc
        (Identifier.id "_")
        List.empty
        body in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match run_check t Term.hole {
        ok _ => true,
        err _ => false,
    }

// KNOWN BUG: Wildcard pattern with arguments should be rejected. The
// wildcard "_" must have zero args.
// FIX: In type_check_match_case, when name is "_", verify args is empty
// and return an error if not.
@[test]
def test_match_wildcard_rejects_args_known_bug : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let body : Term := Term.type_ 1 in
    let case_ : MatchCase := MatchCase.mc
        (Identifier.id "_")
        (List.cons (Identifier.id "x") List.empty)
        body in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match run_check t Term.hole {
        ok _ => true,    // BUG: succeeds when it should fail (wildcard with args)
        err _ => false,   // CORRECT: would be err _ => true after fix
    }

// --- Match tests: scrutinee type resolution ---

// Match on a scrutinee that is a bound variable with a known type.
// The scrutinee's type should be available for constructor validation
// and branch type checking, but none of this is implemented yet.
@[test]
def test_match_bound_scrutinee : Bool :=
    let scrutinee : Term := Term.var 0 (DebugName.unnamed) in
    let body : Term := Term.type_ 1 in
    let case_ : MatchCase := MatchCase.mc
        (Identifier.id "x")
        List.empty
        body in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    let types : List Term := List.cons (Term.type_ 1) List.empty in
    match type_check t Term.hole test_scope types empty_locals {
        ok _ => true,
        err _ => false,
    }

// --- Match tests: branch type unification ---

// KNOWN BUG: When multiple cases are processed, their branch types should be
// unified. Currently only the first case's type is returned.
// Here case1 has type type_1 (infers to type_2) and case2 has a different
// type. Since only the first case is checked, the mismatch is never detected.
// FIX: Check all case bodies, unify their types, and report mismatch if
// unification fails.
@[test]
def test_match_branch_type_conflict_known_bug : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let body1 : Term := Term.type_ 1 in
    let body2 : Term := Term.type_ 0 in
    let case1 : MatchCase := MatchCase.mc (Identifier.id "a") List.empty body1 in
    let case2 : MatchCase := MatchCase.mc (Identifier.id "b") List.empty body2 in
    let cases : List MatchCase := List.cons case1 (List.cons case2 List.empty) in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match run_check t Term.hole {
        ok _ => true,    // BUG: succeeds (only first case checked), should fail
        err _ => false,  // CORRECT: would be err _ => true after fix
    }

// --- Error tests: type mismatch in if ---

@[test]
def test_if_branch_mismatch : Bool :=
    let bool_typ : Term := Term.type_ 1 in
    let cond : Term := Term.var 0 (DebugName.unnamed) in
    let then_ : Term := Term.type_ 1 in
    let else_ : Term := Term.type_ 3 in
    let if_t : Term := Term.lit (Literal.if_ cond then_ else_) in
    let types : List Term := List.cons bool_typ List.empty in
    match type_check if_t Term.hole test_scope types empty_locals {
        ok _ => false,
        err _ => true,
    }

// --- Error tests: app on non-function ---

@[test]
def test_app_non_function : Bool :=
    let t : Term := Term.app (Term.type_ 1) (Term.type_ 1) in
    match run_check t Term.hole {
        ok _ => false,
        err e => match e {
            _ => true,
        },
    }

// --- Complex test: app-lam-pi chain ---

@[test]
def test_lam_app_chain : Bool :=
    let x_dbg : DebugName := DebugName.named (Identifier.id "x") in
    let y_dbg : DebugName := DebugName.named (Identifier.id "y") in
    let arg_a : Term := Term.type_ 1 in
    let arg_b : Term := Term.type_ 1 in
    let ret_typ : Term := Term.type_ 1 in
    let inner_lam : Term := Term.lam y_dbg arg_b (Term.var 0 y_dbg) in
    let outer_lam : Term := Term.lam x_dbg arg_a inner_lam in
    let applied : Term := Term.app (Term.app outer_lam (Term.type_ 1)) (Term.type_ 1) in
    match run_check applied Term.hole {
        ok _ => true,
        err _ => false,
    }

// --- Test: pi-of-pi (higher-kinded type) ---

@[test]
def test_pi_of_pi : Bool :=
    let dbg : DebugName := DebugName.named (Identifier.id "F") in
    let arg : Term := Term.pi (Term.type_ 1) (Term.type_ 1) in
    let body : Term := Term.var 0 dbg in
    let types : List Term := List.cons arg List.empty in
    let t : Term := Term.pi arg body in
    match type_check t Term.hole test_scope types empty_locals {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (Term.type_ 1) },
        err _ => false,
    }
