use lib::types {
  Attribute, DebugName, Decl, FieldPattern, FieldPatternEntry, Identifier,
  InductConstructor, Inductive, MatchCase, ModulePath, NamePath, Param,
  Scope, ScopeClassDef, ScopeData, Similar, Term, TypeError,
  app, forall, hole, id, if_, inductive_d, lam, lit, match_, mc, mk, mp, named,
  not_a_type, pi, type_, unknown_var, unnamed, var,
}
use lib::scope {build_scope_from_decls, scope_find_inductive}
use lib::typecheck::infer {
  TypedTerm, empty_local_types, empty_locals, mk, sentinel, type_check,
  type_check_match_case,
}

open Term {app, forall, hole, lam, lit, pi, type_, var}
open DebugName {named, unnamed}
open Identifier {id}
open ModulePath {mp}
open Literal {if_, match_}
open TypeError {not_a_type, unknown_var}

// --- Test scope setup: empty decl_list with builtins (Type, Prop) ---

def empty_path : ModulePath := ModulePath.mp List.empty
def test_sd : ScopeData := build_scope_from_decls empty_path List.empty
def test_scope : Scope := {
    module_id := empty_path,
    scope := test_sd,
    parent := Option.none,
}

def run_check (t : Term) (e : Term) : Result TypeError TypedTerm :=
    type_check t e test_scope empty_local_types empty_locals

// --- Sort / universe tests ---

#[test]
def test_sort_prop_is_type : Bool :=
    match run_check (Term.type_ 0) (Term.type_ 1) {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_sort_type_is_type1 : Bool :=
    match run_check (Term.type_ 1) (Term.type_ 2) {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_sort_cumulativity_prop_in_type : Bool :=
    match run_check (Term.type_ 0) (Term.type_ 2) {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_sort_cumulativity_type_in_type2 : Bool :=
    match run_check (Term.type_ 1) (Term.type_ 3) {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_sort_reject_too_small : Bool :=
    match run_check (Term.type_ 2) (Term.type_ 1) {
        ok _ => false,
        err e => match e {
            not_a_type _ => true,
            _ => false,
        },
    }

#[test]
def test_sort_infer_prop : Bool :=
    match run_check (Term.type_ 0) Term.hole {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (Term.type_ 1) },
        err _ => false,
    }

#[test]
def test_sort_infer_type : Bool :=
    match run_check (Term.type_ 1) Term.hole {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (Term.type_ 2) },
        err _ => false,
    }

// A sort is never its own type: `Sort n : Sort m` requires `n < m`, so
// `Sort n` checked AGAINST `Sort n` must be rejected. Before this pin,
// `type_check_sort_full`'s `I64.beq expected_level level` arm accepted
// it — a Type-in-Type hole in the self-hosted checker (the Rust core
// rejects it: it infers `Sort (n+1)` and then fails `n+1 <= n`).
//
// Note this hole was reachable only through `Term.type_ N` terms the
// checker constructs itself, NOT through `Sort N` surface syntax:
// `Sort` is registered as a `Term.hole`-signatured free variable
// (`add_builtin_sort`, lang/scope.mo), so `Sort 1` in source lowers to
// an ordinary application and goes through `type_check_app`. Real
// `Sort N` syntax (making this reachable from source) is the next
// step, which is why this fix lands first.
#[test]
def test_sort_not_its_own_type : Bool :=
    match run_check (Term.type_ 1) (Term.type_ 1) {
        ok _ => false,
        err e => match e {
            not_a_type _ => true,
            _ => false,
        },
    }

#[test]
def test_sort_prop_not_its_own_type : Bool :=
    match run_check (Term.type_ 0) (Term.type_ 0) {
        ok _ => false,
        err e => match e {
            not_a_type _ => true,
            _ => false,
        },
    }

// --- Variable tests ---

#[test]
def test_var_bound_simple : Bool :=
    let dbg : DebugName := DebugName.unnamed in
    let types : List Term := List.cons (Term.type_ 1) List.empty in
    match type_check (Term.var 0 dbg) Term.hole test_scope types empty_locals {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (Term.type_ 1) },
        err _ => false,
    }

#[test]
def test_var_bound_oob : Bool :=
    let dbg : DebugName := DebugName.unnamed in
    match type_check (Term.var 0 dbg) Term.hole test_scope empty_local_types empty_locals {
        ok _ => false,
        err e => match e {
            unknown_var _ => true,
            _ => false,
        },
    }

#[test]
def test_var_free_unnamed : Bool :=
    let dbg : DebugName := DebugName.unnamed in
    match run_check (Term.var sentinel dbg) Term.hole {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (Term.type_ 1) },
        err _ => false,
    }

#[test]
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

#[test]
def test_pi_simple : Bool :=
    let t : Term := Term.pi (Term.type_ 1) (Term.type_ 1) in
    match run_check t Term.hole {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (Term.type_ 1) },
        err _ => false,
    }

#[test]
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

#[test]
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

#[test]
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

#[test]
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

#[test]
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

#[test]
def test_app_id : Bool :=
    let x_dbg : DebugName := DebugName.named (Identifier.id "x") in
    let arg_typ : Term := Term.type_ 1 in
    let id_body : Term := Term.var 0 x_dbg in
    let id_lam : Term := Term.lam x_dbg arg_typ id_body in
    // The lambda is `Sort 1 -> Sort 1`, so its argument must have type
    // `Sort 1` -- which `Sort 0` does (`Sort 0 : Sort 1`). This used to
    // be applied to `Term.type_ 1`, which is `Sort 1 : Sort 1` -- true
    // only under the Type-in-Type hole `type_check_sort_full` had.
    let result : Term := Term.app id_lam (Term.type_ 0) in
    match run_check result Term.hole {
        ok _ => true,
        err _ => false,
    }

#[test]
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

#[test]
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

#[test]
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

#[test]
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

#[test]
def test_match_empty_cases : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let t : Term := Term.lit (Literal.match_ scrutinee List.empty) in
    match run_check t Term.hole {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_match_single_case : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let body : Term := Term.type_ 1 in
    let case_ : MatchCase := MatchCase.mc (Identifier.id "x") List.empty body Option.none in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match run_check t Term.hole {
        ok _ => true,
        err _ => false,
    }

// --- Match tests: multi-case processing ---

// BUG: type_check_cases only processes the head case and drops the rest.
// Two cases with both valid bodies: the match succeeds (but rest is ignored).
#[test]
def test_match_multi_case_bodies_ok : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let body1 : Term := Term.type_ 1 in
    let body2 : Term := Term.type_ 1 in
    let case1 : MatchCase := MatchCase.mc (Identifier.id "a") List.empty body1 Option.none in
    let case2 : MatchCase := MatchCase.mc (Identifier.id "b") List.empty body2 Option.none in
    let cases : List MatchCase := List.cons case1 (List.cons case2 List.empty) in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match run_check t Term.hole {
        ok _ => true,
        err _ => false,
    }

// KNOWN BUG: type_check_cases only processes the head case and drops the rest.
// The second case body has a type error, which should be caught.
// All cases are now checked and their types unified.
#[test]
def test_match_multi_case_second_fails : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let body1 : Term := Term.type_ 1 in
    let bad_var : Term := Term.var sentinel (DebugName.named (Identifier.id "no_such")) in
    let case1 : MatchCase := MatchCase.mc (Identifier.id "a") List.empty body1 Option.none in
    let case2 : MatchCase := MatchCase.mc (Identifier.id "b") List.empty bad_var Option.none in
    let cases : List MatchCase := List.cons case1 (List.cons case2 List.empty) in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match run_check t Term.hole {
        ok _ => false,  // Should fail because second case references unknown var
        err _ => true,
    }

// --- Match tests: constructor pattern args ---

// Constructor pattern args are added to the local scope and local_types,
// so the case body can reference them. Pattern arg "x" is now bound with
// Term.hole type before type-checking the case body.
#[test]
def test_match_case_args_bound : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let arg_id : Identifier := Identifier.id "x" in
    let body : Term := Term.var sentinel (DebugName.named arg_id) in
    let case_ : MatchCase := MatchCase.mc
        (Identifier.id "some")
        (List.cons arg_id List.empty)
        body
        Option.none in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match run_check t Term.hole {
        ok _ => true,   // Pattern arg "x" is now bound
        err _ => false,
    }

// --- Match tests: constructor validation with inductive ---

// Build a scope containing a simple Maybe-like inductive.
// Maybe has constructors: some (with one field), none (no fields).
def maybe_scope : Scope :=
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let type_name : NamePath := NamePath.npath (List.cons (Identifier.id "Maybe") List.empty) in
    let some_cn : InductConstructor := InductConstructor.mk
        (NamePath.npath (List.cons (Identifier.id "some") List.empty))
        List.empty
        (Term.type_ 1) in
    let none_cn : InductConstructor := InductConstructor.mk
        (NamePath.npath (List.cons (Identifier.id "none") List.empty))
        List.empty
        (Term.type_ 1) in
    let cns : List InductConstructor := List.cons some_cn (List.cons none_cn List.empty) in
    let empty_params : List Param := List.empty in
    let empty_attrs : List Attribute := List.empty in
    let ind : Inductive := Inductive.mk
        type_name empty_params (Term.type_ 1) cns empty_attrs Visibility.package_private in
    let decl_list : List Decl := List.cons (Decl.inductive_d ind) List.empty in
    let sd : ScopeData := build_scope_from_decls mod_path decl_list in
    {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    }

#[test]
def test_match_inductive_in_scope : Bool :=
    match scope_find_inductive (NamePath.npath (List.cons (Identifier.id "Maybe") List.empty)) maybe_scope {
        ok _ => true,
        err _ => false,
    }

// Match on a scrutinee with a valid constructor name. Constructor validation
// looks up the constructor in the inductive and verifies it exists.
#[test]
def test_match_valid_constructor : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let body : Term := Term.type_ 1 in
    let case_ : MatchCase := MatchCase.mc
        (Identifier.id "some")
        List.empty
        body
        Option.none in
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
// Second constructor "bogus" is not in Maybe — should be rejected.
// validate_cases_against_inductive finds Maybe via "some" constructor,
// then rejects "bogus" which is not in Maybe's constructors.
#[test]
def test_match_invalid_constructor : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let body : Term := Term.type_ 1 in
    let case_some : MatchCase := MatchCase.mc
        (Identifier.id "some")
        List.empty
        body
        Option.none in
    let case_bogus : MatchCase := MatchCase.mc
        (Identifier.id "bogus")
        List.empty
        body
        Option.none in
    let cases : List MatchCase := List.cons case_some (List.cons case_bogus List.empty) in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match type_check t Term.hole maybe_scope empty_local_types empty_locals {
        ok _ => false,    // Should fail because bogus is not a Maybe constructor
        err _ => true,
    }

// --- Match tests: wildcard pattern ---

// Wildcard case (name "_") with no args. Wildcard handling now works
// correctly: args verification and branch type accumulation are implemented.
#[test]
def test_match_wildcard : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let body : Term := Term.type_ 1 in
    let case_ : MatchCase := MatchCase.mc
        (Identifier.id "_")
        List.empty
        body
        Option.none in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match run_check t Term.hole {
        ok _ => true,
        err _ => false,
    }

// Wildcard pattern with arguments should be rejected. The wildcard "_"
// must have zero args. type_check_match_case verifies this and returns
// an error if args is non-empty.
#[test]
def test_match_wildcard_rejects_args : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let body : Term := Term.type_ 1 in
    let case_ : MatchCase := MatchCase.mc
        (Identifier.id "_")
        (List.cons (Identifier.id "x") List.empty)
        body
        Option.none in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match run_check t Term.hole {
        ok _ => false,  // Wildcard with args should fail
        err _ => true,  // Correctly fails
    }

// --- Match tests: scrutinee type resolution ---

// Match on a scrutinee that is a bound variable with a known type.
// The scrutinee's type is now available for constructor validation and
// branch type checking.
#[test]
def test_match_bound_scrutinee : Bool :=
    let scrutinee : Term := Term.var 0 (DebugName.unnamed) in
    let body : Term := Term.type_ 1 in
    let case_ : MatchCase := MatchCase.mc
        (Identifier.id "x")
        List.empty
        body
        Option.none in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    let types : List Term := List.cons (Term.type_ 1) List.empty in
    match type_check t Term.hole test_scope types empty_locals {
        ok _ => true,
        err _ => false,
    }

// --- Match tests: branch type unification ---

// When multiple cases are processed, their branch types should be unified.
// Here case1 has type type_1 (infers to type_2) and case2 has a different
// type. All case bodies are checked and their types are unified, so the
// mismatch is detected.
#[test]
def test_match_branch_type_conflict : Bool :=
    let scrutinee : Term := Term.type_ 1 in
    let body1 : Term := Term.type_ 1 in
    let body2 : Term := Term.type_ 0 in
    let case1 : MatchCase := MatchCase.mc (Identifier.id "a") List.empty body1 Option.none in
    let case2 : MatchCase := MatchCase.mc (Identifier.id "b") List.empty body2 Option.none in
    let cases : List MatchCase := List.cons case1 (List.cons case2 List.empty) in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match run_check t Term.hole {
        ok _ => false,  // Should fail due to type conflict
        err _ => true,  // Correctly detects the conflict
    }

// -------------------------------------------------------------------
// Phase 7 of `plans/implementations/struct-field-destructuring.md`:
// elaboration for match-case field patterns.
// -------------------------------------------------------------------

/// A named single-constructor inductive with NAMED fields (`Maybe`
/// above has none) -- needed to exercise real field-pattern resolution.
def point_ind : Inductive :=
    let type_name : NamePath := NamePath.npath (List.cons (Identifier.id "Point") List.empty) in
    let x_param : Param := Param.mk (Identifier.id "x") (Term.type_ 1) Multiplicity.many Option.none List.empty in
    let y_param : Param := Param.mk (Identifier.id "y") (Term.type_ 1) Multiplicity.many Option.none List.empty in
    let mk_cn : InductConstructor := InductConstructor.mk
        (NamePath.npath (List.cons (Identifier.id "mk") List.empty))
        (List.cons x_param (List.cons y_param List.empty))
        (Term.type_ 1) in
    let cns : List InductConstructor := List.cons mk_cn List.empty in
    let empty_params : List Param := List.empty in
    let empty_attrs : List Attribute := List.empty in
    Inductive.mk type_name empty_params (Term.type_ 1) cns empty_attrs Visibility.package_private

def point_scope : Scope :=
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let decl_list : List Decl := List.cons (Decl.inductive_d point_ind) List.empty in
    let sd : ScopeData := build_scope_from_decls mod_path decl_list in
    {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    }

/// A scrutinee whose OWN type is genuinely known to be `Point`
/// (`type_head_name`'s preferred exact-lookup path, not the
/// constructor-name-scan fallback the OTHER tests in this file lean on
/// -- required here since a BARE `{ .. }` pattern has no name for the
/// fallback scan to use at all).
def point_typed_scrutinee : Term := Term.var 0 DebugName.unnamed
def point_typed_local_types : List Term :=
    List.cons (Term.var sentinel (DebugName.named (Identifier.id "Point"))) List.empty

#[test]
def test_field_pattern_bare_reordered_fields_permutes_body_correctly : Bool :=
    // Written `{ y, x }` (opposite of the constructor's own declared
    // `x, y` order) -- the body references "x" (written SECOND, so at
    // PARSE time it would have been pushed innermost, Term.var 0).
    // After resolution or `term_permute`, the checked case's body must
    // reference "x" at its DECLARED-order position instead (x is
    // declared FIRST, so pushed first/outermost -- Term.var 1, since y
    // is declared last/innermost) -- this is the exact thing a missing
    // or buggy permute would get wrong while still "succeeding".
    let x_entry : FieldPatternEntry := FieldPatternEntry.mk (Identifier.id "x") (Identifier.id "x") in
    let y_entry : FieldPatternEntry := FieldPatternEntry.mk (Identifier.id "y") (Identifier.id "y") in
    let fp : FieldPattern := FieldPattern.mk (List.cons y_entry (List.cons x_entry List.empty)) false in
    let args : List Identifier := List.cons (Identifier.id "y") (List.cons (Identifier.id "x") List.empty) in
    let body : Term := Term.var 0 DebugName.unnamed in
    let case_ : MatchCase := MatchCase.mc (Identifier.id "") args body (Option.some fp) in
    match type_check_match_case case_ point_typed_scrutinee (Term.var sentinel (DebugName.named (Identifier.id "Point"))) (Option.some point_ind) Term.hole point_scope point_typed_local_types empty_locals {
        err _ => false,
        ok checked =>
            match checked {
                mk resolved_case _typ =>
                    match resolved_case {
                        MatchCase.mc resolved_name resolved_args resolved_body resolved_fp =>
                            Similar.similar resolved_name (Identifier.id "mk")
                                && I64.beq (List.length resolved_args) 2
                                && (match resolved_body { Term.var idx _ => I64.beq idx 1, _ => false })
                                && (match resolved_fp { Option.none => true, Option.some _ => false }),
                    },
            },
    }

#[test]
def test_field_pattern_named_multi_constructor_via_named_form : Bool :=
    // The NAMED form resolves via the same constructor-name-scan
    // fallback the OTHER (positional) tests in this file already rely
    // on -- no need for a typed scrutinee here.
    let x_entry : FieldPatternEntry := FieldPatternEntry.mk (Identifier.id "x") (Identifier.id "px") in
    let fp : FieldPattern := FieldPattern.mk (List.cons x_entry List.empty) true in
    let args : List Identifier := List.cons (Identifier.id "x") List.empty in
    let body : Term := Term.var 0 DebugName.unnamed in
    let case_ : MatchCase := MatchCase.mc (Identifier.id "mk") args body (Option.some fp) in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ (Term.type_ 1) cases) in
    match type_check t Term.hole point_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_field_pattern_bare_form_multi_constructor_is_an_error : Bool :=
    // A bare `{ .. }` pattern needs a genuinely single-constructor
    // inductive to resolve at all -- construct a two-constructor scope
    // and confirm resolution is rejected (via the SAME typed-scrutinee
    // setup the reordering test above uses, so `maybe_ind` really does
    // resolve to a real (multi-constructor) inductive rather than
    // `Option.none` short-circuiting with an unrelated error message).
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let type_name : NamePath := NamePath.npath (List.cons (Identifier.id "Shape") List.empty) in
    let r_param : Param := Param.mk (Identifier.id "r") (Term.type_ 1) Multiplicity.many Option.none List.empty in
    let circle_cn : InductConstructor := InductConstructor.mk (NamePath.npath (List.cons (Identifier.id "circle") List.empty)) (List.cons r_param List.empty) (Term.type_ 1) in
    let square_cn : InductConstructor := InductConstructor.mk (NamePath.npath (List.cons (Identifier.id "square") List.empty)) (List.cons r_param List.empty) (Term.type_ 1) in
    let cns : List InductConstructor := List.cons circle_cn (List.cons square_cn List.empty) in
    let empty_params : List Param := List.empty in
    let empty_attrs : List Attribute := List.empty in
    let ind : Inductive := Inductive.mk type_name empty_params (Term.type_ 1) cns empty_attrs Visibility.package_private in
    let decl_list : List Decl := List.cons (Decl.inductive_d ind) List.empty in
    let sd : ScopeData := build_scope_from_decls mod_path decl_list in
    let shape_scope : Scope := { module_id := mod_path, scope := sd, parent := Option.none } in
    let scrutinee : Term := Term.var 0 DebugName.unnamed in
    let types : List Term := List.cons (Term.var sentinel (DebugName.named (Identifier.id "Shape"))) List.empty in
    let fp : FieldPattern := FieldPattern.mk List.empty true in
    let case_ : MatchCase := MatchCase.mc (Identifier.id "") List.empty (Term.type_ 1) (Option.some fp) in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match type_check t Term.hole shape_scope types empty_locals {
        ok _ => false,
        err _ => true,
    }

#[test]
def test_field_pattern_unknown_field_is_an_error : Bool :=
    let fp : FieldPattern := FieldPattern.mk (List.cons (FieldPatternEntry.mk (Identifier.id "z") (Identifier.id "z")) List.empty) true in
    let case_ : MatchCase := MatchCase.mc (Identifier.id "mk") (List.cons (Identifier.id "z") List.empty) (Term.type_ 1) (Option.some fp) in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ (Term.type_ 1) cases) in
    match type_check t Term.hole point_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

#[test]
def test_field_pattern_missing_field_without_rest_is_an_error : Bool :=
    // Only "x" is listed, no `..` -- "y" is uncovered.
    let fp : FieldPattern := FieldPattern.mk (List.cons (FieldPatternEntry.mk (Identifier.id "x") (Identifier.id "x")) List.empty) false in
    let case_ : MatchCase := MatchCase.mc (Identifier.id "mk") (List.cons (Identifier.id "x") List.empty) (Term.type_ 1) (Option.some fp) in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ (Term.type_ 1) cases) in
    match type_check t Term.hole point_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

// --- Error tests: type mismatch in if ---

#[test]
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

#[test]
def test_app_non_function : Bool :=
    let t : Term := Term.app (Term.type_ 1) (Term.type_ 1) in
    match run_check t Term.hole {
        ok _ => false,
        err e => match e {
            _ => true,
        },
    }

// --- Complex test: app-lam-pi chain ---

#[test]
def test_lam_app_chain : Bool :=
    let x_dbg : DebugName := DebugName.named (Identifier.id "x") in
    let y_dbg : DebugName := DebugName.named (Identifier.id "y") in
    let arg_a : Term := Term.type_ 1 in
    let arg_b : Term := Term.type_ 1 in
    let ret_typ : Term := Term.type_ 1 in
    let inner_lam : Term := Term.lam y_dbg arg_b (Term.var 0 y_dbg) in
    let outer_lam : Term := Term.lam x_dbg arg_a inner_lam in
    // Both lambdas are `Sort 1 -> ...`, so both arguments must have type
    // `Sort 1` -- `Sort 0` does. See `test_app_id` above: passing
    // `Term.type_ 1` here asserted `Sort 1 : Sort 1`.
    let applied : Term := Term.app (Term.app outer_lam (Term.type_ 0)) (Term.type_ 0) in
    match run_check applied Term.hole {
        ok _ => true,
        err _ => false,
    }

// --- Test: pi-of-pi (higher-kinded type) ---

#[test]
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

// --- Test: class method resolution ---

// Scope with a single class method "beq" with type signature Type.
def classdef_scope : Scope :=
    let beq_id : Identifier := Identifier.id "beq" in
    let beq_class : NamePath := NamePath.npath (List.cons (Identifier.id "BEq") List.empty) in
    let beq_np : NamePath := NamePath.npath (List.cons beq_id List.empty) in
    let scd : ScopeClassDef := {
        class_name := beq_class,
        full_name := beq_np,
        name := beq_id,
        sig := Term.type_ 1,
    } in
    let base_sd : ScopeData := test_sd in
    let sd_with_cd : ScopeData := { base_sd with class_defs := List.cons scd base_sd.class_defs } in
    { module_id := empty_path, scope := sd_with_cd, parent := Option.none }

#[test]
def test_class_method_resolve : Bool :=
    let t : Term := Term.var sentinel (DebugName.named (Identifier.id "beq")) in
    match type_check t Term.hole classdef_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

// --- Test: unknown class method still fails ---

#[test]
def test_class_method_unknown : Bool :=
    let t : Term := Term.var sentinel (DebugName.named (Identifier.id "nope")) in
    match type_check t Term.hole classdef_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

// --- Test: class method type is used as term type ---

#[test]
def test_class_method_type : Bool :=
    let t : Term := Term.var sentinel (DebugName.named (Identifier.id "beq")) in
    match type_check t Term.hole classdef_scope empty_local_types empty_locals {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (Term.type_ 1) },
        err _ => false,
    }

/// A char literal types as `Char`, the same way a string literal types as
/// `String` -- `def c : Char := 'M'` used to be untypeable because
/// `type_check_lit` had no `Literal.char` arm at all (a runtime
/// non-exhaustive-match crash, not a diagnostic).
#[test]
def test_char_literal_types_as_char : Bool :=
    let t : Term := Term.lit (Literal.char (Char.of_bytes (String.to_list "M"))) in
    match type_check t Term.hole test_scope empty_local_types empty_locals {
        ok tt =>
            match tt.typ {
                Term.var _idx dbg =>
                    match dbg {
                        DebugName.named n => Similar.similar n (Identifier.id "Char"),
                        DebugName.unnamed => false,
                    },
                _ => false,
            },
        err _ => false,
    }

// --- Duplicate bare type names across modules (`find_inductive_by_type_
// head_or_scan`) -------------------------------------------------------
//
// `type_head_name` yields a BARE name and `scope_find_inductive` keys on
// bare names, so in codegen's whole-program scope (`build_scope_from_
// decls` over every loaded module at once) two modules declaring the same
// type name are indistinguishable and the winner is module load order.
// `lang/types.mo`'s `Decl` and `init/meta.mo`'s `Decl` are such a pair.
// Both orders are asserted so the fallback is exercised whichever wins.

def dup_type_name : NamePath := NamePath.npath (List.cons (Identifier.id "Dup") List.empty)

/// A `Dup` whose constructors do NOT cover the match below -- stands in
/// for `init/meta.mo`'s `Decl` (`d_def`/`d_instance`/`d_error`).
def dup_other_ind : Inductive :=
    let p : Param := Param.mk (Identifier.id "p") (Term.type_ 1) Multiplicity.many Option.none List.empty in
    let a_cn : InductConstructor := InductConstructor.mk
        (NamePath.npath (List.cons (Identifier.id "d_other_a") List.empty))
        (List.cons p List.empty) (Term.type_ 1) in
    let b_cn : InductConstructor := InductConstructor.mk
        (NamePath.npath (List.cons (Identifier.id "d_other_b") List.empty))
        (List.cons p List.empty) (Term.type_ 1) in
    let cns : List InductConstructor := List.cons a_cn (List.cons b_cn List.empty) in
    let empty_params : List Param := List.empty in
    let empty_attrs : List Attribute := List.empty in
    Inductive.mk dup_type_name empty_params (Term.type_ 1) cns empty_attrs Visibility.package_private

/// The `Dup` the match is actually about -- stands in for `lang/types.mo`'s
/// `Decl` (the one carrying `infix_d`).
def dup_wanted_ind : Inductive :=
    let p : Param := Param.mk (Identifier.id "p") (Term.type_ 1) Multiplicity.many Option.none List.empty in
    let w_cn : InductConstructor := InductConstructor.mk
        (NamePath.npath (List.cons (Identifier.id "d_wanted") List.empty))
        (List.cons p List.empty) (Term.type_ 1) in
    let cns : List InductConstructor := List.cons w_cn List.empty in
    let empty_params : List Param := List.empty in
    let empty_attrs : List Attribute := List.empty in
    Inductive.mk dup_type_name empty_params (Term.type_ 1) cns empty_attrs Visibility.package_private

/// `match (v : Dup) { d_wanted p => Type }` against a scope holding both
/// `Dup`s in the given order.
def dup_match_checks (decl_list : List Decl) : Bool :=
    let mod_id : Identifier := Identifier.id "DupTest" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let sd : ScopeData := build_scope_from_decls mod_path decl_list in
    let dup_scope : Scope := { module_id := mod_path, scope := sd, parent := Option.none } in
    let scrutinee : Term := Term.var 0 DebugName.unnamed in
    let types : List Term := List.cons (Term.var sentinel (DebugName.named (Identifier.id "Dup"))) List.empty in
    let case_ : MatchCase := MatchCase.mc (Identifier.id "d_wanted") (List.cons (Identifier.id "p") List.empty) (Term.type_ 1) Option.none in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match type_check t Term.hole dup_scope types empty_locals {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_dup_type_name_other_declared_first : Bool :=
    dup_match_checks (List.cons (Decl.inductive_d dup_other_ind) (List.cons (Decl.inductive_d dup_wanted_ind) List.empty))

#[test]
def test_dup_type_name_wanted_declared_first : Bool :=
    dup_match_checks (List.cons (Decl.inductive_d dup_wanted_ind) (List.cons (Decl.inductive_d dup_other_ind) List.empty))
