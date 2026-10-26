use std::list {List.length}
use lang::types {
  Attribute, Binder, BinderInfo, DebugName, Decl, Def, Elim, FieldPattern, FieldPatternEntry,
  Identifier, CubicalPrim, InductConstructor, Inductive, MatchCase, ModulePath,
  NamePath, Param, Scope, ScopeClassDef, ScopeData, Similar, SortLevel, Term, TypeError,
  binder_anon, binder_binder, binder_explicit, binder_named, char, cub_i0, cub_i1, cub_ijoin,
  cub_imeet, cub_ineg,
  cub_interval, if_, many, match_, package_private, sentinel, sort_n,
  cub,
}
use lib::module {try_parse_decls}
use lib::scope {build_scope_from_decls, scope_find_inductive}
use lib::typecheck::diagnostic {type_error_message}
use lib::typecheck::infer {
  CalleeDomain, TypedTerm, ctor_index_values, derive_motive, elaborate_if_to_elim, elaborate_match_to_elim,
  empty_local_types, empty_locals,
  is_uninformative_carrier, lam_binder_hint, match_coverage_warning, type_check,
  type_check_elim, type_check_match_case
}
use lib::typecheck::subst {term_shift}

open Term {app, hole, lam, lit, pi, var}
open DebugName {named, unnamed}
open Identifier {id}
open ModulePath {mp}
open Literal {if_, match_}
open TypeError {not_a_type, unknown_var}

// --- Test scope setup: empty decl_list with builtins (Type, Prop) ---

def empty_path : ModulePath := ModulePath.mk List.empty
def test_sd : ScopeData := build_scope_from_decls empty_path List.empty
def test_scope : Scope := {
    module_id := empty_path,
    scope := test_sd,
    parent := Option.none,
    incomplete_match_ok := false,
}

def run_check (t : Term) (e : Term) : Result TypeError TypedTerm :=
    type_check t e test_scope empty_local_types empty_locals

// --- Sort / universe tests ---

#[test]
def test_sort_prop_is_type : Bool :=
    match run_check (sort_n 0) (sort_n 1) {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_sort_type_is_type1 : Bool :=
    match run_check (sort_n 1) (sort_n 2) {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_sort_cumulativity_prop_in_type : Bool :=
    match run_check (sort_n 0) (sort_n 2) {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_sort_cumulativity_type_in_type2 : Bool :=
    match run_check (sort_n 1) (sort_n 3) {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_sort_reject_too_small : Bool :=
    match run_check (sort_n 2) (sort_n 1) {
        ok _ => false,
        err e => match e {
            not_a_type _ => true,
            _ => false,
        },
    }

#[test]
def test_sort_infer_prop : Bool :=
    match run_check (sort_n 0) Term.hole {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (sort_n 1) },
        err _ => false,
    }

#[test]
def test_sort_infer_type : Bool :=
    match run_check (sort_n 1) Term.hole {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (sort_n 2) },
        err _ => false,
    }

// A sort is never its own type: `Sort n : Sort m` requires `n < m`, so
// `Sort n` checked AGAINST `Sort n` must be rejected. Before this pin,
// `type_check_sort_full`'s `I64.beq expected_level level` arm accepted
// it — a Type-in-Type hole in the self-hosted checker (the Rust core
// rejects it: it infers `Sort (n+1)` and then fails `n+1 <= n`).
//
// Note this hole was reachable only through the sort TERMS the checker
// (and these fixtures) construct themselves, NOT through `Sort N`
// surface syntax:
// `Sort` is registered as a `Term.hole`-signatured free variable
// (`add_builtin_sort`, lang/scope.mo), so `Sort 1` in source lowers to
// an ordinary application and goes through `type_check_app`. Real
// `Sort N` syntax (making this reachable from source) is the next
// step, which is why this fix lands first.
#[test]
def test_sort_not_its_own_type : Bool :=
    match run_check (sort_n 1) (sort_n 1) {
        ok _ => false,
        err e => match e {
            not_a_type _ => true,
            _ => false,
        },
    }

#[test]
def test_sort_prop_not_its_own_type : Bool :=
    match run_check (sort_n 0) (sort_n 0) {
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
    let types : List Term := [sort_n 1] in
    match type_check (Term.var 0 dbg) Term.hole test_scope types empty_locals {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ (sort_n 1) },
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
            match tt { mk _ typ => Similar.similar typ (sort_n 1) },
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
//
// The universe a `Pi`/`Forall` INFERS is the `max` of its components'
// sorts (W1.2), not the flat level-1 universe these tests used to assert.
// A component contributes the sort of its TYPE: `Type` is `Sort 1`, so
// `Type : Sort 2` and `(A : Type) -> Type` is itself a `Sort 2`. Three
// of the four affected tests are below; the fourth, `test_quantifier_infer`,
// is in the quantifier section and says the same thing about the other arm.
// They were the corpus's only pins on the old rule, and `monad test` is
// what found them: `check` never validates a signature's KIND, so no
// `check`-based comparison can see a universe move.

#[test]
def test_pi_simple : Bool :=
    let t : Term := Term.pi binder_anon (sort_n 1) (sort_n 1) in
    match run_check t Term.hole {
        ok tt =>
            // Both components are `Type`, contributing 2 each.
            match tt { mk _ typ => Similar.similar typ (sort_n 2) },
        err _ => false,
    }

#[test]
def test_pi_dependent : Bool :=
    let dbg : DebugName := DebugName.named (Identifier.id "A") in
    let arg : Term := sort_n 1 in
    let ret : Term := Term.var 0 dbg in
    let t : Term := Term.pi binder_anon arg ret in
    let types : List Term := List.cons arg List.empty in
    match type_check t Term.hole test_scope types empty_locals {
        ok tt =>
            // The domain `Type` contributes 2; the body's type is
            // `A`'s own local type, `Type`, contributing 1 -- so the
            // `max` is still 2, and the domain is what decides it.
            match tt { mk _ typ => Similar.similar typ (sort_n 2) },
        err _ => false,
    }

#[test]
def test_pi_arg_is_not_type : Bool :=
    let id : Identifier := Identifier.id "x" in
    let dbg : DebugName := DebugName.named id in
    let var_term : Term := Term.var sentinel dbg in
    let t : Term := Term.pi binder_anon var_term (sort_n 1) in
    match run_check t Term.hole {
        ok _ => false,
        err _ => true,
    }

// --- Lambda tests ---

#[test]
def test_lam_check_mode : Bool :=
    let dbg : DebugName := DebugName.named (Identifier.id "x") in
    let body : Term := Term.var 0 dbg in
    let arg_typ : Term := sort_n 1 in
    let expected : Term := Term.pi binder_anon arg_typ arg_typ in
    let lam : Term := Term.lam (binder_explicit dbg) arg_typ body in
    match run_check lam expected {
        ok tt =>
            match tt { mk _ typ => Similar.similar typ expected },
        err _ => false,
    }

#[test]
def test_lam_infer_mode : Bool :=
    let dbg : DebugName := DebugName.named (Identifier.id "x") in
    let body : Term := Term.var 0 dbg in
    let arg_typ : Term := sort_n 1 in
    let lam : Term := Term.lam (binder_explicit dbg) arg_typ body in
    match run_check lam Term.hole {
        ok tt =>
            match tt { mk _ typ =>
                match typ {
                    pi _ a _ => Similar.similar a arg_typ,
                    _ => false,
                }},
        err _ => false,
    }

#[test]
def test_lam_unnamed : Bool :=
    let dbg : DebugName := DebugName.unnamed in
    let body : Term := Term.var 0 dbg in
    let arg_typ : Term := sort_n 1 in
    let expected : Term := Term.pi binder_anon arg_typ arg_typ in
    let lam : Term := Term.lam (binder_explicit dbg) arg_typ body in
    match run_check lam expected {
        ok _ => true,
        err _ => false,
    }

// --- Application tests ---

#[test]
def test_app_id : Bool :=
    let x_dbg : DebugName := DebugName.named (Identifier.id "x") in
    let arg_typ : Term := sort_n 1 in
    let id_body : Term := Term.var 0 x_dbg in
    let id_lam : Term := Term.lam (binder_explicit x_dbg) arg_typ id_body in
    // The lambda is `Sort 1 -> Sort 1`, so its argument must have type
    // `Sort 1` -- which `Sort 0` does (`Sort 0 : Sort 1`). This used to
    // be applied to `Sort 1`, which is `Sort 1 : Sort 1` -- true only
    // under the Type-in-Type hole `type_check_sort_full` had.
    let result : Term := Term.app id_lam (sort_n 0) in
    match run_check result Term.hole {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_app_with_hole_return : Bool :=
    let x_dbg : DebugName := DebugName.named (Identifier.id "x") in
    let arg_typ : Term := sort_n 1 in
    let id_body : Term := Term.var 0 x_dbg in
    let id_lam : Term := Term.lam (binder_explicit x_dbg) arg_typ id_body in
    let result : Term := Term.app id_lam (sort_n 0) in
    match run_check result Term.hole {
        ok _ => true,
        err _ => false,
    }

// --- Quantifier tests ---
//
// `Term.pi` with a `binder` tag, which is what `Term.forall` became in R2b.

#[test]
def test_quantifier_infer : Bool :=
    let a_id : Identifier := Identifier.id "A" in
    let kind : Term := sort_n 1 in
    let body : Term := sort_n 1 in
    let t : Term := Term.pi (binder_binder a_id) kind body in
    match run_check t Term.hole {
        ok tt =>
            // Same rule on the quantifier flavour of `Term.pi`: both
            // components are `Type`, contributing 2 each (see the note
            // above the Pi tests).
            match tt { mk _ typ => Similar.similar typ (sort_n 2) },
        err _ => false,
    }

#[test]
def test_quantifier_unnamed : Bool :=
    // Built as a literal rather than through `binder_binder`, which wraps
    // every name it is handed in `DebugName.named`: what this pins is the
    // UNNAMED spelling. Annotated local first -- the
    // bare-struct-literal-in-argument-position miscompile.
    let b : Binder := { name := DebugName.unnamed, info := BinderInfo.binder } in
    let kind : Term := sort_n 1 in
    let body : Term := sort_n 1 in
    let t : Term := Term.pi b kind body in
    match run_check t Term.hole {
        ok _ => true,
        err _ => false,
    }

// --- If tests ---

#[test]
def test_if_simple : Bool :=
    let cond : Term := Term.var 0 (DebugName.unnamed) in
    let then_ : Term := sort_n 1 in
    let else_ : Term := sort_n 1 in
    let if_t : Term := Term.lit (Literal.if_ cond then_ else_) in
    let bool_typ : Term := sort_n 1 in
    let types : List Term := List.cons bool_typ List.empty in
    match type_check if_t Term.hole test_scope types empty_locals {
        ok _ => true,
        err _ => false,
    }

// --- Match tests (basic structure) ---

#[test]
def test_match_empty_cases : Bool :=
    let scrutinee : Term := sort_n 1 in
    let t : Term := Term.lit (Literal.match_ scrutinee List.empty) in
    match run_check t Term.hole {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_match_single_case : Bool :=
    let scrutinee : Term := sort_n 1 in
    let body : Term := sort_n 1 in
    let case_ : MatchCase := MatchCase.mk (Identifier.id "x") List.empty body Option.none Option.none in
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
    let scrutinee : Term := sort_n 1 in
    let body1 : Term := sort_n 1 in
    let body2 : Term := sort_n 1 in
    let case1 : MatchCase := MatchCase.mk (Identifier.id "a") List.empty body1 Option.none Option.none in
    let case2 : MatchCase := MatchCase.mk (Identifier.id "b") List.empty body2 Option.none Option.none in
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
    let scrutinee : Term := sort_n 1 in
    let body1 : Term := sort_n 1 in
    let bad_var : Term := Term.var sentinel (DebugName.named (Identifier.id "no_such")) in
    let case1 : MatchCase := MatchCase.mk (Identifier.id "a") List.empty body1 Option.none Option.none in
    let case2 : MatchCase := MatchCase.mk (Identifier.id "b") List.empty bad_var Option.none Option.none in
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
    let scrutinee : Term := sort_n 1 in
    let arg_id : Identifier := Identifier.id "x" in
    let body : Term := Term.var sentinel (DebugName.named arg_id) in
    let case_ : MatchCase := MatchCase.mk
        (Identifier.id "some")
        (List.cons arg_id List.empty)
        body
        Option.none Option.none in
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
    let mod_path : ModulePath := ModulePath.mk (List.cons mod_id List.empty) in
    let type_name : NamePath := NamePath.mk (List.cons (Identifier.id "Maybe") List.empty) in
    let some_cn : InductConstructor := InductConstructor.mk
        (NamePath.mk (List.cons (Identifier.id "some") List.empty))
        List.empty
        (sort_n 1) in
    let none_cn : InductConstructor := InductConstructor.mk
        (NamePath.mk (List.cons (Identifier.id "none") List.empty))
        List.empty
        (sort_n 1) in
    let cns : List InductConstructor := List.cons some_cn (List.cons none_cn List.empty) in
    let empty_params : List Param := List.empty in
    let empty_attrs : List Attribute := List.empty in
    let ind : Inductive := Inductive.mk
        type_name empty_params (sort_n 1) cns empty_attrs Visibility.package_private in
    let decl_list : List Decl := List.cons (Decl.inductive_d ind) List.empty in
    let sd : ScopeData := build_scope_from_decls mod_path decl_list in
    {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
        incomplete_match_ok := false,
    }

#[test]
def test_match_inductive_in_scope : Bool :=
    match scope_find_inductive (NamePath.mk (List.cons (Identifier.id "Maybe") List.empty)) maybe_scope {
        ok _ => true,
        err _ => false,
    }

// Match on a scrutinee with a valid constructor name. Constructor validation
// looks up the constructor in the inductive and verifies it exists.
#[test]
def test_match_valid_constructor : Bool :=
    let scrutinee : Term := sort_n 1 in
    let body : Term := sort_n 1 in
    let case_some : MatchCase := MatchCase.mk
        (Identifier.id "some")
        List.empty
        body
        Option.none Option.none in
    // `none` is named too, and not in order to test it: since Phase 1
    // (strict-exhaustiveness.md) a `Maybe` match omitting `none` is a
    // coverage ERROR, so this arm is what keeps the pin about VALID
    // constructor names rather than about exhaustiveness.
    let case_none : MatchCase := MatchCase.mk
        (Identifier.id "none")
        List.empty
        body
        Option.none Option.none in
    let cases : List MatchCase := List.cons case_some (List.cons case_none List.empty) in
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
    let scrutinee : Term := sort_n 1 in
    let body : Term := sort_n 1 in
    let case_some : MatchCase := MatchCase.mk
        (Identifier.id "some")
        List.empty
        body
        Option.none Option.none in
    let case_bogus : MatchCase := MatchCase.mk
        (Identifier.id "bogus")
        List.empty
        body
        Option.none Option.none in
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
    let scrutinee : Term := sort_n 1 in
    let body : Term := sort_n 1 in
    let case_ : MatchCase := MatchCase.mk
        (Identifier.id "_")
        List.empty
        body
        Option.none Option.none in
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
    let scrutinee : Term := sort_n 1 in
    let body : Term := sort_n 1 in
    let case_ : MatchCase := MatchCase.mk
        (Identifier.id "_")
        (List.cons (Identifier.id "x") List.empty)
        body
        Option.none Option.none in
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
    let body : Term := sort_n 1 in
    let case_ : MatchCase := MatchCase.mk
        (Identifier.id "x")
        List.empty
        body
        Option.none Option.none in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    let types : List Term := [sort_n 1] in
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
    let scrutinee : Term := sort_n 1 in
    let body1 : Term := sort_n 1 in
    let body2 : Term := sort_n 0 in
    let case1 : MatchCase := MatchCase.mk (Identifier.id "a") List.empty body1 Option.none Option.none in
    let case2 : MatchCase := MatchCase.mk (Identifier.id "b") List.empty body2 Option.none Option.none in
    let cases : List MatchCase := List.cons case1 (List.cons case2 List.empty) in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match run_check t Term.hole {
        ok _ => false,  // Should fail due to type conflict
        err _ => true,  // Correctly detects the conflict
    }

// --- Match exhaustiveness (strict-exhaustiveness.md, Phase 1) ---
//
// These pins call `match_coverage_warning` DIRECTLY -- the rule's pure query,
// and the same one the reporting side consumes. The rule is a pure function of
// (cases, maybe_ind, scope), and `maybe_ind` is the whole of the type
// information it consumes, so testing it needs no scope plumbing at all. The
// end-to-end pins at the end go through `type_check`, to prove the call in
// `type_check_cases_accum`'s tail is live AND that it no longer fails the
// check -- the rule is a warning (see `validate_match_coverage`'s own note).

/// A closed three-constructor inductive, declared in the order `c`, `d`, `e`
/// -- which is the order the diagnostic must list them in.
def cov_ctor (n : String) : InductConstructor :=
    InductConstructor.mk
        (NamePath.mk (List.cons (Identifier.id n) List.empty))
        List.empty
        (sort_n 1)

def cov_ind : Inductive :=
    Inductive.mk
        (NamePath.mk (List.cons (Identifier.id "T") List.empty))
        List.empty
        (sort_n 1)
        [cov_ctor "c", cov_ctor "d", cov_ctor "e"]
        List.empty
        Visibility.package_private

def cov_case (n : String) : MatchCase :=
    MatchCase.mk (Identifier.id n) List.empty (sort_n 1) Option.none Option.none

// These drive `match_coverage_warning`, the rule's pure QUERY, and not
// `validate_match_coverage`: the rule is a WARNING now, so the latter
// answers `ok` for a covered and an uncovered match alike and a test
// reading it would pass vacuously -- the one kind of gate worth less than
// no gate at all. `match_coverage_warning` is also what the reporting side
// consumes, so these keep testing the thing that is actually wired up, and
// they go on meaning the same when the rule is flipped back to an error.
def cov_ok (cases : List MatchCase) : Bool :=
    match match_coverage_warning cases (Option.some cov_ind) test_scope {
        Option.none => true,
        Option.some _ => false,
    }

def cov_msg (cases : List MatchCase) : String :=
    match match_coverage_warning cases (Option.some cov_ind) test_scope {
        Option.none => "",
        Option.some msg => msg,
    }

#[test]
def test_match_covering_every_constructor_passes : Bool :=
    cov_ok [cov_case "c", cov_case "d", cov_case "e"]

#[test]
def test_match_missing_one_constructor_is_an_error : Bool :=
    not (cov_ok [cov_case "c", cov_case "d"])

#[test]
def test_match_missing_arm_message_names_the_type_and_constructor : Bool :=
    String.beq (cov_msg [cov_case "c", cov_case "d"])
        "non-exhaustive match: `T.e` is not covered (add an arm for it, or a `_` arm)"

#[test]
def test_match_missing_two_arms_listed_in_declaration_order : Bool :=
    String.beq (cov_msg [cov_case "c"])
        "non-exhaustive match: `T.d`, `T.e` are not covered (add arms for them, or a `_` arm)"

#[test]
def test_match_wildcard_last_covers_everything : Bool :=
    cov_ok [cov_case "c", cov_case "_"]

#[test]
def test_match_wildcard_first_covers_everything : Bool :=
    cov_ok [cov_case "_", cov_case "c"]

#[test]
def test_match_zero_constructor_inductive_needs_no_empty_match : Bool :=
    // The inverse rule -- "0 constructors therefore require an empty match"
    // -- is deliberately NOT implemented, and this is what pins that. A case
    // naming nothing real is caught by `validate_cases_against_inductive`
    // instead; coverage itself is vacuously satisfied with no constructors.
    let voidish : Inductive := Inductive.mk
        (NamePath.mk (List.cons (Identifier.id "V") List.empty))
        List.empty (sort_n 1) List.empty List.empty Visibility.package_private in
    match match_coverage_warning [cov_case "c"] (Option.some voidish) test_scope {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_match_unresolved_scrutinee_is_skipped : Bool :=
    match match_coverage_warning [cov_case "c"] Option.none test_scope {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_match_incomplete_match_exemption_switches_the_rule_off : Bool :=
    let exempt : Scope := { test_scope with incomplete_match_ok := true } in
    match match_coverage_warning [cov_case "c"] (Option.some cov_ind) exempt {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_match_bare_field_pattern_name_covers_nothing : Bool :=
    // `""` is the parser's placeholder for a bare `{ .. }` field pattern. It
    // cannot occur once the cases are checked, so reaching it means a
    // resolution hole -- and covering nothing over-reports, the safe way.
    not (cov_ok [cov_case "c", cov_case "d", cov_case ""])

// --- the same rule end to end, through the checker ---

#[test]
def test_match_missing_arm_now_fails_the_check_end_to_end : Bool :=
    // The rule is an ERROR again (strict-exhaustiveness.md Phase 4, flipped
    // once the corpus was swept clean). This is the inverse of the pin that
    // used to live here under the warning regime -- see that era's note,
    // still true in reverse: when this returns `err`, the error reaches
    // codegen through `elaborate_def_with_scope`, whose caller
    // (`elaborate_module_decls_reporting`) is best-effort and SWALLOWS it,
    // which is why `scope_for_elab_body` (lang/module.mo) keeps elaboration
    // exempt regardless -- only `check`'s path is meant to see this `err`.
    let scrutinee : Term := sort_n 1 in
    let body : Term := sort_n 1 in
    let case_some : MatchCase := MatchCase.mk (Identifier.id "some") List.empty body Option.none Option.none in
    let cases : List MatchCase := List.cons case_some List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match type_check t Term.hole maybe_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

/// The error path, not just the pure query: the rejected `type_check` call
/// above still names the missing constructor in its rendered message,
/// mirroring `test_match_missing_arm_message_names_the_type_and_constructor`
/// but through the real entry point rather than `match_coverage_warning`
/// directly -- a check that errored for the wrong reason would pass the pin
/// above and be worthless.
#[test]
def test_match_missing_arm_error_names_the_constructor_end_to_end : Bool :=
    let scrutinee : Term := sort_n 1 in
    let body : Term := sort_n 1 in
    let case_some : MatchCase := MatchCase.mk (Identifier.id "some") List.empty body Option.none Option.none in
    let cases : List MatchCase := List.cons case_some List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match type_check t Term.hole maybe_scope empty_local_types empty_locals {
        ok _ => false,
        err e => String.contains (type_error_message e) "`Maybe.none`",
    }

/// `#[allow_incomplete_match]`'s effect through the real entry point: with
/// the exemption set, the SAME incomplete match that just failed above must
/// type-check. `test_match_incomplete_match_exemption_switches_the_rule_off`
/// pins the pure query only; this is its `type_check`-level counterpart, so
/// a regression that wires the exemption into the query but not into the
/// checker's own call site would still be caught.
#[test]
def test_match_incomplete_match_exemption_still_checks_end_to_end : Bool :=
    let exempt_scope : Scope := { maybe_scope with incomplete_match_ok := true } in
    let scrutinee : Term := sort_n 1 in
    let body : Term := sort_n 1 in
    let case_some : MatchCase := MatchCase.mk (Identifier.id "some") List.empty body Option.none Option.none in
    let cases : List MatchCase := List.cons case_some List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match type_check t Term.hole exempt_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

/// The same shape as the pin above, but asserting the rule still SEES the
/// gap and still names the missing constructor -- a warning that reports
/// nothing would satisfy the pin above and be worthless.
#[test]
def test_match_missing_arm_is_still_reported_end_to_end : Bool :=
    let type_name : NamePath := NamePath.mk (List.cons (Identifier.id "Maybe") List.empty) in
    let some_cn : InductConstructor := InductConstructor.mk
        (NamePath.mk (List.cons (Identifier.id "some") List.empty)) List.empty (sort_n 1) in
    let none_cn : InductConstructor := InductConstructor.mk
        (NamePath.mk (List.cons (Identifier.id "none") List.empty)) List.empty (sort_n 1) in
    let ind : Inductive := Inductive.mk
        type_name List.empty (sort_n 1) [some_cn, none_cn] List.empty Visibility.package_private in
    let case_some : MatchCase := MatchCase.mk (Identifier.id "some") List.empty (sort_n 1) Option.none Option.none in
    match match_coverage_warning [case_some] (Option.some ind) test_scope {
        Option.some msg => String.contains msg "`Maybe.none`",
        Option.none => false,
    }

#[test]
def test_match_exhaustive_arms_check_end_to_end : Bool :=
    let scrutinee : Term := sort_n 1 in
    let body : Term := sort_n 1 in
    let case_some : MatchCase := MatchCase.mk (Identifier.id "some") List.empty body Option.none Option.none in
    let case_none : MatchCase := MatchCase.mk (Identifier.id "none") List.empty body Option.none Option.none in
    let cases : List MatchCase := List.cons case_some (List.cons case_none List.empty) in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match type_check t Term.hole maybe_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

// -------------------------------------------------------------------
// Phase 7 of `plans/implementations/struct-field-destructuring.md`:
// elaboration for match-case field patterns.
// -------------------------------------------------------------------

/// A named single-constructor inductive with NAMED fields (`Maybe`
/// above has none) -- needed to exercise real field-pattern resolution.
def point_ind : Inductive :=
    let type_name : NamePath := NamePath.mk (List.cons (Identifier.id "Point") List.empty) in
    let x_param : Param := Param.mk (Identifier.id "x") (sort_n 1) Multiplicity.many Option.none List.empty in
    let y_param : Param := Param.mk (Identifier.id "y") (sort_n 1) Multiplicity.many Option.none List.empty in
    let mk_cn : InductConstructor := InductConstructor.mk
        (NamePath.mk (List.cons (Identifier.id "mk") List.empty))
        (List.cons x_param (List.cons y_param List.empty))
        (sort_n 1) in
    let cns : List InductConstructor := List.cons mk_cn List.empty in
    let empty_params : List Param := List.empty in
    let empty_attrs : List Attribute := List.empty in
    Inductive.mk type_name empty_params (sort_n 1) cns empty_attrs Visibility.package_private

def point_scope : Scope :=
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mk (List.cons mod_id List.empty) in
    let decl_list : List Decl := List.cons (Decl.inductive_d point_ind) List.empty in
    let sd : ScopeData := build_scope_from_decls mod_path decl_list in
    {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
        incomplete_match_ok := false,
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
    let case_ : MatchCase := MatchCase.mk (Identifier.id "") args body (Option.some fp) Option.none in
    match type_check_match_case case_ point_typed_scrutinee (Term.var sentinel (DebugName.named (Identifier.id "Point"))) (Option.some point_ind) Term.hole point_scope point_typed_local_types empty_locals {
        err _ => false,
        ok checked =>
            match checked {
                mk resolved_case _typ =>
                    match resolved_case {
                        MatchCase.mk resolved_name resolved_args resolved_body resolved_fp _resolved_tn =>
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
    let case_ : MatchCase := MatchCase.mk (Identifier.id "mk") args body (Option.some fp) Option.none in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ (sort_n 1) cases) in
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
    let mod_path : ModulePath := ModulePath.mk (List.cons mod_id List.empty) in
    let type_name : NamePath := NamePath.mk (List.cons (Identifier.id "Shape") List.empty) in
    let r_param : Param := Param.mk (Identifier.id "r") (sort_n 1) Multiplicity.many Option.none List.empty in
    let circle_cn : InductConstructor := InductConstructor.mk (NamePath.mk [Identifier.id "circle"]) [r_param] (sort_n 1) in
    let square_cn : InductConstructor := InductConstructor.mk (NamePath.mk [Identifier.id "square"]) [r_param] (sort_n 1) in
    let cns : List InductConstructor := List.cons circle_cn (List.cons square_cn List.empty) in
    let empty_params : List Param := List.empty in
    let empty_attrs : List Attribute := List.empty in
    let ind : Inductive := Inductive.mk type_name empty_params (sort_n 1) cns empty_attrs Visibility.package_private in
    let decl_list : List Decl := List.cons (Decl.inductive_d ind) List.empty in
    let sd : ScopeData := build_scope_from_decls mod_path decl_list in
    let shape_scope : Scope := { module_id := mod_path, scope := sd, parent := Option.none, incomplete_match_ok := false } in
    let scrutinee : Term := Term.var 0 DebugName.unnamed in
    let types : List Term := List.cons (Term.var sentinel (DebugName.named (Identifier.id "Shape"))) List.empty in
    let fp : FieldPattern := FieldPattern.mk List.empty true in
    let case_ : MatchCase := MatchCase.mk (Identifier.id "") List.empty (sort_n 1) (Option.some fp) Option.none in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ scrutinee cases) in
    match type_check t Term.hole shape_scope types empty_locals {
        ok _ => false,
        err _ => true,
    }

#[test]
def test_field_pattern_unknown_field_is_an_error : Bool :=
    let fp : FieldPattern := FieldPattern.mk (List.cons (FieldPatternEntry.mk (Identifier.id "z") (Identifier.id "z")) List.empty) true in
    let case_ : MatchCase := MatchCase.mk (Identifier.id "mk") [Identifier.id "z"] (sort_n 1) (Option.some fp) Option.none in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ (sort_n 1) cases) in
    match type_check t Term.hole point_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

#[test]
def test_field_pattern_missing_field_without_rest_is_an_error : Bool :=
    // Only "x" is listed, no `..` -- "y" is uncovered.
    let fp : FieldPattern := FieldPattern.mk (List.cons (FieldPatternEntry.mk (Identifier.id "x") (Identifier.id "x")) List.empty) false in
    let case_ : MatchCase := MatchCase.mk (Identifier.id "mk") [Identifier.id "x"] (sort_n 1) (Option.some fp) Option.none in
    let cases : List MatchCase := List.cons case_ List.empty in
    let t : Term := Term.lit (Literal.match_ (sort_n 1) cases) in
    match type_check t Term.hole point_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

// --- A GENERIC inductive: field types must be instantiated ---
//
// `point_ind` above declares `empty_params`, so no test built on it can
// say whether a field pattern instantiates the inductive's own type
// parameters -- which is exactly how
// `plans/implementations/field-pattern-type-args-not-substituted.md`
// stayed latent while the whole block above was green. `pair_ind`'s
// constructor fields are declared over its OWN params (`first : A`,
// `second : B`), the shape a generic inductive's constructor really has
// once its own check has skolemized them into free named vars.
//
// These rows assert the field's TYPE, not the absence of a diagnostic:
// the defect's dangerous half was silent (a bare binding absorbed the
// wrong type instead of reporting it), so only a test that reads the
// type back can fail if it returns. The source-level companions live in
// `lang/src/module.mo` (`field_pattern_preamble`).

def named_free_var (name : String) : Term := Term.var sentinel (DebugName.named (Identifier.id name))

def term_is_named_var (t : Term) (name : String) : Bool :=
    match t {
        Term.var _idx dbg =>
            match dbg {
                DebugName.named nid => Similar.similar nid (Identifier.id name),
                DebugName.unnamed => false,
            },
        _ => false,
    }

def pair_ind : Inductive :=
    let type_name : NamePath := NamePath.mk [Identifier.id "P"] in
    let a_param : Param := Param.mk (Identifier.id "A") (sort_n 1) Multiplicity.many Option.none List.empty in
    let b_param : Param := Param.mk (Identifier.id "B") (sort_n 1) Multiplicity.many Option.none List.empty in
    let first_param : Param := Param.mk (Identifier.id "first") (named_free_var "A") Multiplicity.many Option.none List.empty in
    let second_param : Param := Param.mk (Identifier.id "second") (named_free_var "B") Multiplicity.many Option.none List.empty in
    let ctor : InductConstructor := InductConstructor.mk (NamePath.mk [Identifier.id "mk"]) [first_param, second_param] (sort_n 1) in
    Inductive.mk type_name [a_param, b_param] (sort_n 1) [ctor] List.empty Visibility.package_private

def pair_scope : Scope :=
    let mod_path : ModulePath := ModulePath.mk [Identifier.id "Test"] in
    let sd : ScopeData := build_scope_from_decls mod_path [Decl.inductive_d pair_ind] in
    {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
        incomplete_match_ok := false,
    }

/// `P T U` -- two DIFFERENT concrete arguments, so substituting the wrong
/// parameter is a visible failure and not an accident that still passes.
def pair_scrutinee_typ : Term := Term.app (Term.app (named_free_var "P") (named_free_var "T")) (named_free_var "U")
def pair_typed_local_types : List Term := List.cons pair_scrutinee_typ List.empty

/// The arm's body IS the field binder, so the checked case's body type is
/// the type the field pattern bound it to. `T` after the fix; `A` -- the
/// inductive's own parameter, a free sentinel nothing ever solves -- before.
#[test]
def test_field_pattern_first_field_type_comes_from_the_scrutinee : Bool :=
    let entry : FieldPatternEntry := FieldPatternEntry.mk (Identifier.id "first") (Identifier.id "first") in
    let fp : FieldPattern := FieldPattern.mk (List.cons entry List.empty) true in
    let args : List Identifier := List.cons (Identifier.id "first") List.empty in
    let case_ : MatchCase := MatchCase.mk (Identifier.id "") args (Term.var 0 DebugName.unnamed) (Option.some fp) Option.none in
    match type_check_match_case case_ (Term.var 0 DebugName.unnamed) pair_scrutinee_typ (Option.some pair_ind) Term.hole pair_scope pair_typed_local_types empty_locals {
        err _ => false,
        ok checked =>
            match checked {
                mk _resolved_case body_typ => term_is_named_var body_typ "T",
            },
    }

/// The second field, which is what says the substitution pairs each
/// parameter with its OWN argument rather than mapping both to the first.
#[test]
def test_field_pattern_second_field_type_comes_from_the_scrutinee : Bool :=
    let entry : FieldPatternEntry := FieldPatternEntry.mk (Identifier.id "second") (Identifier.id "second") in
    let fp : FieldPattern := FieldPattern.mk (List.cons entry List.empty) true in
    let args : List Identifier := List.cons (Identifier.id "second") List.empty in
    let case_ : MatchCase := MatchCase.mk (Identifier.id "") args (Term.var 0 DebugName.unnamed) (Option.some fp) Option.none in
    match type_check_match_case case_ (Term.var 0 DebugName.unnamed) pair_scrutinee_typ (Option.some pair_ind) Term.hole pair_scope pair_typed_local_types empty_locals {
        err _ => false,
        ok checked =>
            match checked {
                mk _resolved_case body_typ => term_is_named_var body_typ "U",
            },
    }

/// A scrutinee type carrying NO arguments at all (the bare head `P`, which
/// is what an un-inferred scrutinee looks like): the substitution has
/// nothing to zip, and must leave the declared types alone rather than
/// erroring or dropping fields. Pins `substitute_inductive_type_params`'s
/// documented partial-information fallback through this path too.
#[test]
def test_field_pattern_bare_scrutinee_head_leaves_declared_types : Bool :=
    let entry : FieldPatternEntry := FieldPatternEntry.mk (Identifier.id "first") (Identifier.id "first") in
    let fp : FieldPattern := FieldPattern.mk (List.cons entry List.empty) true in
    let args : List Identifier := List.cons (Identifier.id "first") List.empty in
    let case_ : MatchCase := MatchCase.mk (Identifier.id "") args (Term.var 0 DebugName.unnamed) (Option.some fp) Option.none in
    match type_check_match_case case_ (Term.var 0 DebugName.unnamed) (named_free_var "P") (Option.some pair_ind) Term.hole pair_scope (List.cons (named_free_var "P") List.empty) empty_locals {
        err _ => false,
        ok checked =>
            match checked {
                mk _resolved_case body_typ => term_is_named_var body_typ "A",
            },
    }

// -------------------------------------------------------------------
// The GATE on an unannotated lambda argument's discovered binder type
// (`lam_binder_hint`, `lang/src/typecheck/infer.mo`).
//
// The discovery exists for the do-bind shape (`implementations/
// do-bind-binder-untyped.md`), and its first corpus run found that handing
// over a domain the callee had NOT finished solving is worse than handing
// over nothing: `Foldable.foldr (fn x acc => x + acc) 0 [1, 2, 3]` and
// `MonadState.modify_get (fn n => ...)` got a binder typed as the leaked
// signature variable (`B`, `S`) instead of a hole, carrier inference read
// that variable, and the emitted dictionary called itself until the driver
// died -- `driver exited -1` on `init/src/foldable_tests.mo`, `init/src/
// foldable_tests_fold.mo` and `examples/state_monad.mo`, all three of which
// the pre-change compiler ran clean. The pins below are that finding: each
// rejection is a shape the ungated version accepted.
//
// `pair_scope` declares the inductive `P`, so `P` is a name the scope
// resolves and `B` is not -- exactly the two cases the gate separates.
// -------------------------------------------------------------------

def cd_of (dom : Term) (vars : List Identifier) : CalleeDomain :=
    CalleeDomain.mk dom vars

/// The accepting case: a domain that is a real, closed type and that the
/// callee's own declaration does not bind -- the do-bind / callback shape
/// the fix is for.
#[test]
def test_lam_binder_hint_accepts_a_closed_type : Bool :=
    match lam_binder_hint (cd_of (named_free_var "P") List.empty) pair_scope {
        Option.none => false,
        Option.some bt => term_is_named_var bt "P",
    }

/// A free name that resolves to nothing is a type VARIABLE. This is the
/// foldable regression, and it is the reason the gate is not optional.
#[test]
def test_lam_binder_hint_rejects_an_unresolved_name : Bool :=
    match lam_binder_hint (cd_of (named_free_var "B") List.empty) pair_scope {
        Option.none => true,
        Option.some _ => false,
    }

/// A name the callee's OWN declaration binds is rejected even when the
/// scope happens to resolve it as a type: a class parameter is a variable
/// to the call site however the scope reads its name. `state_monad.mo`'s
/// rejection is this arm -- its domain was the class's own `S`.
#[test]
def test_lam_binder_hint_rejects_a_declared_name_that_resolves : Bool :=
    match lam_binder_hint (cd_of (named_free_var "P") (List.cons (Identifier.id "P") List.empty)) pair_scope {
        Option.none => true,
        Option.some _ => false,
    }

/// A HOLE domain says nothing, which is exactly what the parser wrote for
/// the unannotated lambda -- so there is no discovery and the argument
/// keeps the old behavior rather than gaining a meaningless annotation.
#[test]
def test_lam_binder_hint_rejects_a_hole : Bool :=
    match lam_binder_hint (cd_of Term.hole List.empty) pair_scope {
        Option.none => true,
        Option.some _ => false,
    }

/// A function-typed domain is read for its ARROW domain, which is what the
/// lambda's parameter becomes (`Monad.bind`'s continuation parameter is
/// `A -> M B`, and the binder is its `A`). The codomain is deliberately NOT
/// part of the test -- the caller hands over `Term.pi bt Term.hole`, so an
/// unsolved `Q` there can never reach a binder.
#[test]
def test_lam_binder_hint_reads_the_arrow_domain : Bool :=
    let dom : Term := Term.pi binder_anon (named_free_var "P") (named_free_var "Q") in
    match lam_binder_hint (cd_of dom List.empty) pair_scope {
        Option.none => false,
        Option.some bt => term_is_named_var bt "P",
    }

// --- Error tests: type mismatch in if ---

#[test]
def test_if_branch_mismatch : Bool :=
    let bool_typ : Term := sort_n 1 in
    let cond : Term := Term.var 0 (DebugName.unnamed) in
    let then_ : Term := sort_n 1 in
    let else_ : Term := sort_n 3 in
    let if_t : Term := Term.lit (Literal.if_ cond then_ else_) in
    let types : List Term := List.cons bool_typ List.empty in
    match type_check if_t Term.hole test_scope types empty_locals {
        ok _ => false,
        err _ => true,
    }

// --- Error tests: app on non-function ---

#[test]
def test_app_non_function : Bool :=
    let t : Term := Term.app (sort_n 1) (sort_n 1) in
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
    let arg_a : Term := sort_n 1 in
    let arg_b : Term := sort_n 1 in
    let ret_typ : Term := sort_n 1 in
    let inner_lam : Term := Term.lam (binder_explicit y_dbg) arg_b (Term.var 0 y_dbg) in
    let outer_lam : Term := Term.lam (binder_explicit x_dbg) arg_a inner_lam in
    // Both lambdas are `Sort 1 -> ...`, so both arguments must have type
    // `Sort 1` -- `Sort 0` does. See `test_app_id` above: passing
    // `Sort 1` here asserted `Sort 1 : Sort 1`.
    let applied : Term := Term.app (Term.app outer_lam (sort_n 0)) (sort_n 0) in
    match run_check applied Term.hole {
        ok _ => true,
        err _ => false,
    }

// --- Test: pi-of-pi (higher-kinded type) ---

#[test]
def test_pi_of_pi : Bool :=
    let dbg : DebugName := DebugName.named (Identifier.id "F") in
    let arg : Term := Term.pi binder_anon (sort_n 1) (sort_n 1) in
    let body : Term := Term.var 0 dbg in
    let types : List Term := List.cons arg List.empty in
    let t : Term := Term.pi binder_anon arg body in
    match type_check t Term.hole test_scope types empty_locals {
        ok tt =>
            // The domain is the inner `Pi`, which infers `Sort 2`; the
            // body `F`'s own type IS that inner `Pi`, which is not a
            // sort, so it contributes `level_of_type`'s default of 1.
            // `max (2) (1)` is 2.
            match tt { mk _ typ => Similar.similar typ (sort_n 2) },
        err _ => false,
    }

// --- Test: class method resolution ---

// Scope with a single class method "beq" with type signature Type.
def classdef_scope : Scope :=
    let beq_id : Identifier := Identifier.id "beq" in
    let beq_class : NamePath := NamePath.mk (List.cons (Identifier.id "BEq") List.empty) in
    let beq_np : NamePath := NamePath.mk (List.cons beq_id List.empty) in
    let scd : ScopeClassDef := {
        class_name := beq_class,
        full_name := beq_np,
        name := beq_id,
        sig := sort_n 1,
    } in
    let base_sd : ScopeData := test_sd in
    let sd_with_cd : ScopeData := { base_sd with class_defs := List.cons scd base_sd.class_defs } in
    { module_id := empty_path, scope := sd_with_cd, parent := Option.none, incomplete_match_ok := false }

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
            match tt { mk _ typ => Similar.similar typ (sort_n 1) },
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

def dup_type_name : NamePath := NamePath.mk (List.cons (Identifier.id "Dup") List.empty)

/// A `Dup` whose constructors do NOT cover the match below -- stands in
/// for `init/meta.mo`'s `Decl` (`d_def`/`d_instance`/`d_error`).
def dup_other_ind : Inductive :=
    let p : Param := Param.mk (Identifier.id "p") (sort_n 1) Multiplicity.many Option.none List.empty in
    let a_cn : InductConstructor := InductConstructor.mk
        (NamePath.mk (List.cons (Identifier.id "d_other_a") List.empty))
        [p] (sort_n 1) in
    let b_cn : InductConstructor := InductConstructor.mk
        (NamePath.mk (List.cons (Identifier.id "d_other_b") List.empty))
        [p] (sort_n 1) in
    let cns : List InductConstructor := List.cons a_cn (List.cons b_cn List.empty) in
    let empty_params : List Param := List.empty in
    let empty_attrs : List Attribute := List.empty in
    Inductive.mk dup_type_name empty_params (sort_n 1) cns empty_attrs Visibility.package_private

/// The `Dup` the match is actually about -- stands in for `lang/types.mo`'s
/// `Decl` (the one carrying `infix_d`).
def dup_wanted_ind : Inductive :=
    let p : Param := Param.mk (Identifier.id "p") (sort_n 1) Multiplicity.many Option.none List.empty in
    let w_cn : InductConstructor := InductConstructor.mk
        (NamePath.mk (List.cons (Identifier.id "d_wanted") List.empty))
        [p] (sort_n 1) in
    let cns : List InductConstructor := List.cons w_cn List.empty in
    let empty_params : List Param := List.empty in
    let empty_attrs : List Attribute := List.empty in
    Inductive.mk dup_type_name empty_params (sort_n 1) cns empty_attrs Visibility.package_private

/// `match (v : Dup) { d_wanted p => Type }` against a scope holding both
/// `Dup`s in the given order.
def dup_match_checks (decl_list : List Decl) : Bool :=
    let mod_id : Identifier := Identifier.id "DupTest" in
    let mod_path : ModulePath := ModulePath.mk (List.cons mod_id List.empty) in
    let sd : ScopeData := build_scope_from_decls mod_path decl_list in
    let dup_scope : Scope := { module_id := mod_path, scope := sd, parent := Option.none, incomplete_match_ok := false } in
    let scrutinee : Term := Term.var 0 DebugName.unnamed in
    let types : List Term := List.cons (Term.var sentinel (DebugName.named (Identifier.id "Dup"))) List.empty in
    let case_ : MatchCase := MatchCase.mk (Identifier.id "d_wanted") [Identifier.id "p"] (sort_n 1) Option.none Option.none in
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

// --- A `forall`-headed expected type must still check the lambda's body ---
//
// `type_check_lam` used to match only `Term.pi` and a catch-all that INFERS,
// so a `forall`-headed expected type -- which is what `elaborate_type` produces
// for every polymorphic def, and for any def whose declared type mentions a
// name that is not a top-level decl -- fell into the catch-all and the
// expectation was discarded outright. The body, and every match arm inside it,
// was then checked against `Term.hole`, i.e. not checked.
//
// These pin the fix at term level deliberately. A source-level pin through
// `typecheck_source` (`lang/src/tests/typecheck_examples_tests.mo`) does not
// reproduce it: that helper builds a synthetic single-module scope, and the
// over-generalization that produces the `forall` depends on which names count
// as known, so the bug is reachable there only through an explicit implicit
// binder. Building the quantifier by hand tests the arm itself.
//
// The body `Sort 1` against an expected return of `Sort 1` is rejected by the
// `Sort n : Sort n` rule, so it is a mismatch the checker is known to catch --
// which is what makes the NEGATIVE pin below meaningful rather than a test of
// some unrelated permissiveness.

/// The Pi the two quantifier pins wrap: `Type -> Type`.
def quantifier_pin_pi : Term := Term.pi binder_anon (sort_n 1) (sort_n 1)

/// `{a : Type} -> Type -> Type` -- the shape `{A : Type}` elaborates to, a
/// `Term.pi` whose binder carries the `binder` tag (R2b; this was
/// `Term.forall`).
def quantifier_pin_expected : Term :=
    Term.pi (binder_binder (Identifier.id "a")) (sort_n 1) quantifier_pin_pi

/// NEGATIVE, and the actual regression: the body is `Sort 1` where the Pi's
/// return is `Sort 1`, which `type_check_sort_full` rejects. Before the
/// quantifier arm existed this was ACCEPTED, because the expected type never
/// reached the body.
#[test]
def test_quantifier_expected_still_rejects_bad_body : Bool :=
    match run_check (Term.lam binder_anon (sort_n 1) (sort_n 1)) quantifier_pin_expected {
        ok _ => false,
        err _ => true,
    }

/// POSITIVE control: the same shape with a body that does check. Without this,
/// the pin above would also pass if the arm simply rejected everything.
#[test]
def test_quantifier_expected_still_accepts_good_body : Bool :=
    match run_check (Term.lam binder_anon (sort_n 1) (sort_n 0)) quantifier_pin_expected {
        ok _ => true,
        err _ => false,
    }

/// The un-wrapped control: a plain `Term.pi` expectation already rejected this
/// body, so this pin is what says the quantifier case now agrees with it rather
/// than being special.
#[test]
def test_plain_pi_expected_rejects_bad_body : Bool :=
    match run_check (Term.lam binder_anon (sort_n 1) (sort_n 1)) quantifier_pin_pi {
        ok _ => false,
        err _ => true,
    }

// --- Cubical Stage 1: the interval ---------------------------------------
//
// Term-level, like the sort pins above, and for the same reason: there is no
// surface syntax for a cubical primitive yet (scope binding for the names
// lands in a later Stage 1 commit), so a source-level pin could not reach
// these rules at all.
//
// The rules under test: `I : Type`, `i0 : I`, `i1 : I`, `ineg : I -> I`,
// `imeet`/`ijoin : I -> I -> I`.

#[test]
def test_cubical_interval_is_a_type : Bool :=
    match run_check cub_interval (sort_n 1) {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_cubical_endpoints_inhabit_the_interval : Bool :=
    match run_check cub_i0 cub_interval {
        ok _ => match run_check cub_i1 cub_interval {
            ok _ => true,
            err _ => false,
        },
        err _ => false,
    }

/// NEGATIVE: an endpoint is not a type. Without this the pin above would
/// pass against an arm that accepted anything.
#[test]
def test_cubical_endpoint_is_not_a_type : Bool :=
    match run_check cub_i0 (sort_n 1) {
        ok _ => false,
        err _ => true,
    }

/// NEGATIVE: the interval type is not an interval ELEMENT.
#[test]
def test_cubical_interval_does_not_inhabit_itself : Bool :=
    match run_check cub_interval cub_interval {
        ok _ => false,
        err _ => true,
    }

#[test]
def test_cubical_ineg_is_interval_valued : Bool :=
    match run_check (cub_ineg cub_i0) cub_interval {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_cubical_imeet_and_ijoin_are_interval_valued : Bool :=
    match run_check (cub_imeet cub_i0 cub_i1) cub_interval {
        ok _ => match run_check (cub_ijoin cub_i0 cub_i1) cub_interval {
            ok _ => true,
            err _ => false,
        },
        err _ => false,
    }

/// An argument must be a dimension, not an arbitrary term. This is the pin
/// that says `check_cubical_args` actually checks.
#[test]
def test_cubical_rejects_a_non_interval_argument : Bool :=
    match run_check (cub_ineg (sort_n 1)) cub_interval {
        ok _ => false,
        err _ => true,
    }

/// `args`' length IS the arity, so a malformed application is representable
/// and `type_check_cubical` is the only thing that rejects it. Both
/// directions: too few and too many.
#[test]
def test_cubical_rejects_wrong_arity : Bool :=
    let no_args : Term := cub CubicalPrim.ineg List.empty in
    let two_args : Term := cub CubicalPrim.ineg [cub_i0, cub_i1] in
    match run_check no_args cub_interval {
        ok _ => false,
        err _ => match run_check two_args cub_interval {
            ok _ => false,
            err _ => true,
        },
    }

// --- The interval is a primitive kind (Stage 1 step 4) ---
//
// `is_uninformative_carrier` decides whether a Pi domain can be an
// instance-resolution carrier. The interval must count as uninformative
// like a hole or a sort: an `I -> A` binder is a DIMENSION binder and
// says nothing about `A`'s value, so without this arm
// `carrier_from_pi_chain` reports `I` as the carrier of every `I -> A`
// and instance resolution silently picks wrong.

/// The bare interval is a universe placeholder in the same sense a sort
/// is -- pinned directly, because the arm is a leaf rule and the
/// observable route through instance resolution needs a class and an
/// instance to even reach it.
#[test]
def test_interval_is_an_uninformative_carrier : Bool :=
    is_uninformative_carrier cub_interval

/// Interval-VALUED is not interval: `i0` and `ineg i0` are dimensions,
/// not the kind itself, so they stay carrier candidates -- the arm tests
/// bare-interval-ness, not interval-typedness.
#[test]
def test_a_dimension_is_not_an_uninformative_carrier : Bool :=
    not (is_uninformative_carrier cub_i0)
        && not (is_uninformative_carrier (cub_ineg cub_i0))

/// An ordinary term variable is informative, and the pre-existing arms
/// still hold: the negative control that says adding the interval arm
/// did not quietly widen the predicate.
#[test]
def test_a_term_variable_is_not_an_uninformative_carrier : Bool :=
    not (is_uninformative_carrier (var 0 (named (id "x"))))
        && is_uninformative_carrier Term.hole
        && is_uninformative_carrier (sort_n 1)

// ─── W1.4: level instantiation at call sites ──────────────────────────
//
// The observable is the CALL'S INFERRED TYPE, not an accept/reject: the
// end-to-end paths are lenient about an expectation (`try_type_check_def_call`
// falls back to the unrefined return type instead of erroring), so before
// this step `lift Prop` type-checked with the signature's free `Sort u`
// still in it and nothing downstream objected. Here the type itself is
// read back.
//
// The fixture def is built by hand rather than parsed. Importing
// `lib::module` (for `parse_all_decls`) pulls `lang::parser` into the test
// binary's closure, where ITS `test_if_simple` collides with this file's
// own test of that name and the generated driver miscompiles -- measured
// as a SIGSEGV (`driver exited -1`) that a fresh probe without the import
// does not reproduce.

def lift_def : Def :=
    let u : Identifier := id "u" in
    let a : Identifier := id "A" in
    let level : Term := Term.sort (SortLevel.var u) in
    let params : List Param := [Param.mk a level Multiplicity.many Option.none List.empty] in
    let lift_name : NamePath := NamePath.mk [id "lift"] in
    Def.mk lift_name (pi (binder_named a) level level) (var 0 (named a))
           List.empty List.empty Visibility.package_private params

/// A VALUE def (`three : I64`): its declared type is not a sort, so a call
/// whose parameter is `Sort u` gets no level evidence from it.
def three_def : Def :=
    let i64_ty : Term := var sentinel (named (id "I64")) in
    let three_name : NamePath := NamePath.mk [id "three"] in
    Def.mk three_name i64_ty Term.hole
           List.empty List.empty Visibility.package_private List.empty

def scope_with_decls (decl_list : List Decl) : Scope := {
    module_id := empty_path,
    scope := build_scope_from_decls empty_path decl_list,
    parent := Option.none,
    incomplete_match_ok := false,
}

def lift_scope : Scope := scope_with_decls [Decl.def_d lift_def]
def lift_value_scope : Scope := scope_with_decls [Decl.def_d lift_def, Decl.def_d three_def]

def lift_call (arg : Term) : Term :=
    app (var sentinel (named (id "lift"))) arg

def checked_typ_is (t : Term) (scope : Scope) (want : Term) : Bool :=
    match type_check t hole scope empty_local_types empty_locals {
        err _ => false,
        ok tt => match tt { mk _ typ => Similar.similar typ want },
    }

def checked_typ_is_a_level_var (t : Term) (scope : Scope) : Bool :=
    match type_check t hole scope empty_local_types empty_locals {
        err _ => false,
        ok tt => match tt {
            mk _ typ => match typ {
                Term.sort level => match level {
                    SortLevel.var _ => true,
                    _ => false,
                },
                _ => false,
            },
        },
    }

/// `lift Prop`: the argument's type is `Sort 1`, so `u` instantiates to 1
/// and the call's type is `Sort 1`. Before W1.4 the same call's type was
/// the signature's free `Sort u`.
#[test]
def test_level_polymorphic_call_instantiates_the_level : Bool :=
    checked_typ_is (lift_call (sort_n 0)) lift_scope (sort_n 1)

/// The SAME def at a second level: `lift (Sort 1)` has type `Sort 2`.
/// A solver that hard-coded the first level it saw passes the test above
/// and fails this one.
#[test]
def test_level_polymorphic_call_instantiates_a_second_level : Bool :=
    checked_typ_is (lift_call (sort_n 1)) lift_scope (sort_n 2)

/// No evidence, no binding: a VALUE argument's type (`I64`) is not a
/// sort, so it says nothing about `u`; `u` stays a variable and the
/// call's type is `Sort u` -- never a defaulted level. This is the
/// non-committal half of `solve_levels`.
#[test]
def test_level_polymorphic_call_without_evidence_keeps_the_variable : Bool :=
    checked_typ_is_a_level_var
        (lift_call (var sentinel (named (id "three"))))
        lift_value_scope

/// `def dup (A : Sort u) (B : Sort u) : Sort u := B` -- TWO
/// level-dependent parameters and a level-dependent return.
def dup_def : Def :=
    let u : Identifier := id "u" in
    let a : Identifier := id "A" in
    let b : Identifier := id "B" in
    let level : Term := Term.sort (SortLevel.var u) in
    let params : List Param := [
        Param.mk a level Multiplicity.many Option.none List.empty,
        Param.mk b level Multiplicity.many Option.none List.empty,
    ] in
    let dup_name : NamePath := NamePath.mk [id "dup"] in
    Def.mk dup_name (pi (binder_named a) level (pi (binder_named b) level level))
           (var 0 (named b)) List.empty List.empty Visibility.package_private params

def dup_scope : Scope := scope_with_decls [Decl.def_d dup_def]

def dup_call (first : Term) (second : Term) : Term :=
    app (app (var sentinel (named (id "dup"))) first) second

/// A pi over two sorts at level `n`, whose components both compare equal
/// to `Sort n` -- name-insensitive by construction, so a solver that
/// instantiated a different level is what fails, not a binder name.
def checked_typ_is_pi_over_sorts (t : Term) (scope : Scope) (n : I64) : Bool :=
    match type_check t hole scope empty_local_types empty_locals {
        err _ => false,
        ok tt => match tt {
            mk _ typ => match typ {
                Term.pi _b dom cod =>
                    Similar.similar dom (sort_n n) && Similar.similar cod (sort_n n),
                _ => false,
            },
        },
    }

/// The level solved from the FIRST argument reaches the later parameter
/// and the result: `dup Prop Prop` checks and its type is `Sort 1`.
#[test]
def test_level_solved_from_an_earlier_argument_reaches_a_later_parameter : Bool :=
    checked_typ_is (dup_call (sort_n 0) (sort_n 0)) dup_scope (sort_n 1)

/// A PARTIAL application keeps the remaining pi chain WITH the level
/// instantiated: `dup Prop : (B : Sort 1) -> Sort 1`.
#[test]
def test_level_polymorphic_partial_application_instantiates : Bool :=
    checked_typ_is_pi_over_sorts
        (app (var sentinel (named (id "dup"))) (sort_n 0)) dup_scope 1

// --- R3b: elaboration into `Elim` (core-term-simplification.md) ---
//
// Pins for `elaborate_if_to_elim`/`elaborate_match_to_elim`
// (`lang/src/typecheck/infer.mo`) -- standalone functions, not wired
// into `type_check_if`/`type_check_match` yet (R3c, gated on R4).
// Exercised directly here instead of through `type_check`.
//
// The multi-element equality checks below are top-level helpers, each
// matching one `List.cons` level at a time -- Monad's match patterns
// take plain variables as a constructor's arguments, not a nested
// parenthesized sub-pattern, so "exactly two elements" is a `List.cons`
// arm whose own tail is matched by a SEPARATE nested `match`, not
// `List.cons x1 (List.cons x2 List.empty)` as one pattern.

def two_terms_eq (xs : List Term) (a : Term) (b : Term) : Bool :=
    match xs {
        List.empty => false,
        List.cons x1 rest =>
            match rest {
                List.empty => false,
                List.cons x2 _rest2 => Similar.similar x1 a && Similar.similar x2 b
            },
    }

def one_term_eq (xs : List Term) (a : Term) : Bool :=
    match xs {
        List.empty => false,
        List.cons x1 _rest => Similar.similar x1 a,
    }

def second_term_eq (xs : List Term) (b : Term) : Bool :=
    match xs {
        List.empty => false,
        List.cons _x1 rest =>
            match rest {
                List.empty => false,
                List.cons x2 _rest2 => Similar.similar x2 b
            },
    }

def bool_name_for_elim_tests : NamePath := NamePath.mk (List.cons (Identifier.id "Bool") List.empty)

/// Two nullary constructors, `true` before `false` -- mirrors
/// `init/src/prelude.mo`'s own declaration order, which is what
/// `elaborate_if_to_elim`'s minor order (`[then, else]`) depends on.
def bool_ind_for_elim_tests : Inductive :=
    let true_cn : InductConstructor := InductConstructor.mk
        (NamePath.mk (List.cons (Identifier.id "true") List.empty)) List.empty (sort_n 1) in
    let false_cn : InductConstructor := InductConstructor.mk
        (NamePath.mk (List.cons (Identifier.id "false") List.empty)) List.empty (sort_n 1) in
    Inductive.mk bool_name_for_elim_tests List.empty (sort_n 1)
        [true_cn, false_cn] List.empty Visibility.package_private

#[test]
def test_elaborate_if_to_elim_builds_bool_elim_with_ordered_minors : Bool :=
    let cond : Term := named_free_var "Cond" in
    let then_term : Term := named_free_var "Then" in
    let else_term : Term := named_free_var "Else" in
    let result_typ : Term := named_free_var "ResultTyp" in
    match elaborate_if_to_elim bool_ind_for_elim_tests cond then_term else_term result_typ {
        Term.elim e =>
            Similar.similar e.inductive bool_name_for_elim_tests
                && (match e.levels { List.empty => true, _ => false })
                && (match e.params { List.empty => true, _ => false })
                && Similar.similar e.scrutinee cond
                && Similar.similar e.motive
                    (Term.lam binder_anon (named_free_var "Bool") (term_shift 1 result_typ))
                && two_terms_eq e.minors then_term else_term,
        _ => false,
    }

/// `circle`/`square`, each with one field `r` -- a multi-constructor,
/// non-generic inductive (no type params to substitute, unlike `pair_ind`
/// below), for pins about MINOR ORDER and the named lambda chain.
def shape_name_for_elim_tests : NamePath := NamePath.mk (List.cons (Identifier.id "Shape") List.empty)

def shape_ind_for_elim_tests : Inductive :=
    let r_param : Param :=
        Param.mk (Identifier.id "r") (named_free_var "I64") Multiplicity.many Option.none List.empty in
    let circle_cn : InductConstructor :=
        InductConstructor.mk (NamePath.mk [Identifier.id "circle"]) [r_param] (sort_n 1) in
    let square_cn : InductConstructor :=
        InductConstructor.mk (NamePath.mk [Identifier.id "square"]) [r_param] (sort_n 1) in
    Inductive.mk shape_name_for_elim_tests List.empty (sort_n 1)
        [circle_cn, square_cn] List.empty Visibility.package_private

def shape_scrutinee_typ_for_elim_tests : Term := named_free_var "Shape"

/// Cases are written SQUARE-then-circle -- the opposite of `Shape`'s own
/// declared order -- so a minor list that merely echoed `cases` back
/// would come out backwards. `missing_constructors_go` already proves
/// coverage is a set test rather than a positional one; this is the same
/// property for `Elim.minors`.
#[test]
def test_elaborate_match_to_elim_minors_follow_declared_order : Bool :=
    let circle_body : Term := named_free_var "CircleBody" in
    let square_body : Term := named_free_var "SquareBody" in
    let circle_case : MatchCase := MatchCase.mk (Identifier.id "circle")
        (List.cons (Identifier.id "r") List.empty) circle_body Option.none Option.none in
    let square_case : MatchCase := MatchCase.mk (Identifier.id "square")
        (List.cons (Identifier.id "r") List.empty) square_body Option.none Option.none in
    let cases : List MatchCase := List.cons square_case (List.cons circle_case List.empty) in
    let scrutinee : Term := Term.var 0 DebugName.unnamed in
    let result_typ : Term := named_free_var "ResultTyp" in
    match elaborate_match_to_elim shape_ind_for_elim_tests shape_scrutinee_typ_for_elim_tests
        scrutinee cases result_typ {
        Term.elim e =>
            two_terms_eq e.minors
                (Term.lam (binder_named (Identifier.id "r")) (named_free_var "I64") circle_body)
                (Term.lam (binder_named (Identifier.id "r")) (named_free_var "I64") square_body),
        _ => false,
    }

/// `square` is covered only by a trailing `_` -- its minor must still
/// bind one `r`-typed argument (the arity `Shape.square` declares), with
/// the wildcard's own BODY shifted up by 1 since it moves under a binder
/// it never references. A minor that forgot the shift would read the
/// wrong index for anything the wildcard body names from further out.
#[test]
def test_elaborate_match_to_elim_wildcard_minor_ignores_and_shifts_fields : Bool :=
    let circle_body : Term := named_free_var "CircleBody" in
    let wildcard_body : Term := Term.var 0 DebugName.unnamed in
    let circle_case : MatchCase := MatchCase.mk (Identifier.id "circle")
        (List.cons (Identifier.id "r") List.empty) circle_body Option.none Option.none in
    let wildcard_case : MatchCase :=
        MatchCase.mk (Identifier.id "_") List.empty wildcard_body Option.none Option.none in
    let cases : List MatchCase := List.cons circle_case (List.cons wildcard_case List.empty) in
    let scrutinee : Term := Term.var 0 DebugName.unnamed in
    let result_typ : Term := named_free_var "ResultTyp" in
    match elaborate_match_to_elim shape_ind_for_elim_tests shape_scrutinee_typ_for_elim_tests
        scrutinee cases result_typ {
        Term.elim e =>
            second_term_eq e.minors (Term.lam binder_anon (named_free_var "I64") (term_shift 1 wildcard_body)),
        _ => false,
    }

/// `pair_ind` (above) is generic over `A`/`B`; `pair_scrutinee_typ` applies
/// it to `T`/`U`. `Elim.params` must carry `[T, U]` (read off the
/// scrutinee type's own application spine), and the single `mk` minor's
/// lambda chain must bind `first`/`second` at the INSTANTIATED types `T`/
/// `U`, not the raw declared `A`/`B` -- the same substitution
/// `arg_types_for_case` already does for `type_check_match_case`
/// (`field-pattern-type-args-not-substituted.md`), now exercised through
/// the elaboration path instead.
#[test]
def test_elaborate_match_to_elim_params_and_field_types_from_scrutinee_spine : Bool :=
    let body : Term := named_free_var "Body" in
    let fields : List Identifier := List.cons (Identifier.id "first") (List.cons (Identifier.id "second") List.empty) in
    let case_ : MatchCase := MatchCase.mk (Identifier.id "mk") fields body Option.none Option.none in
    let cases : List MatchCase := List.cons case_ List.empty in
    let scrutinee : Term := Term.var 0 DebugName.unnamed in
    let result_typ : Term := named_free_var "ResultTyp" in
    match elaborate_match_to_elim pair_ind pair_scrutinee_typ scrutinee cases result_typ {
        Term.elim e =>
            two_terms_eq e.params (named_free_var "T") (named_free_var "U")
                && one_term_eq e.minors
                    (Term.lam (binder_named (Identifier.id "first")) (named_free_var "T")
                        (Term.lam (binder_named (Identifier.id "second")) (named_free_var "U") body)),
        _ => false,
    }

// ─── R4: the `Elim` typing rule (core-term-simplification.md) ───────────
//
// Every pin here calls `type_check_elim` directly on a HAND-BUILT `Elim`
// -- nothing in the live pipeline constructs one yet (R3c, gated on this
// very rule). `Term.hole` stands in for an ordinary minor value wherever
// a pin only needs to exercise the RULE's own plumbing (inductive
// resolution, the scrutinee/params check, the motive's sort check, the
// lockstep ctor/minor walk): `type_check`'s own `Term.hole` arm echoes
// back whatever `expected_type` it is handed, so it type-checks against
// ANY expected type without needing any name in scope to resolve -- the
// same reason `local_types` entries below are themselves bare, otherwise-
// unresolvable free-var references rather than real registered types:
// `type_check_bound_var` returns a local's stored type verbatim, with no
// resolution step, so a bound scrutinee's type only has to match
// `rebuild_call`'s rebuilt expected type STRUCTURALLY.

def bool_scope_for_elim_tests : Scope :=
    let mod_path : ModulePath := ModulePath.mk (List.cons (Identifier.id "Test") List.empty) in
    let sd : ScopeData := build_scope_from_decls mod_path
        (List.cons (Decl.inductive_d bool_ind_for_elim_tests) List.empty) in
    {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
        incomplete_match_ok := false,
    }

def shape_scope_for_elim_tests : Scope :=
    let mod_path : ModulePath := ModulePath.mk (List.cons (Identifier.id "Test") List.empty) in
    let sd : ScopeData := build_scope_from_decls mod_path
        (List.cons (Decl.inductive_d shape_ind_for_elim_tests) List.empty) in
    {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
        incomplete_match_ok := false,
    }

/// A degenerate but well-formed constant motive (`fn _ => Prop`, domain
/// a hole) over two nullary minors -- the happy path for the whole rule's
/// plumbing: inductive resolution, the scrutinee-vs-params check, the
/// motive's sort check, and the lockstep walk over `Bool`'s two
/// constructors.
def elim_result_ok (r : Result TypeError TypedTerm) : Bool :=
    match r { ok _ => true, err _ => false }

def elim_result_err (r : Result TypeError TypedTerm) : Bool :=
    match r { ok _ => false, err _ => true }

#[test]
def test_type_check_elim_bool_constant_motive_checks : Bool :=
    let scrutinee : Term := Term.var 0 DebugName.unnamed in
    let local_types : List Term := List.cons (named_free_var "Bool") List.empty in
    let motive : Term := Term.lam binder_anon Term.hole (sort_n 0) in
    let e : Elim := Elim.mk bool_name_for_elim_tests List.empty List.empty List.empty motive
        (List.cons Term.hole (List.cons Term.hole List.empty)) scrutinee in
    elim_result_ok (type_check_elim e Term.hole bool_scope_for_elim_tests local_types empty_locals)

#[test]
def test_type_check_elim_rejects_unknown_inductive : Bool :=
    let bad_name : NamePath := NamePath.mk (List.cons (Identifier.id "NoSuchInductive") List.empty) in
    let scrutinee : Term := Term.var 0 DebugName.unnamed in
    let local_types : List Term := List.cons (named_free_var "Bool") List.empty in
    let motive : Term := Term.lam binder_anon Term.hole (sort_n 0) in
    let e : Elim := Elim.mk bad_name List.empty List.empty List.empty motive
        (List.cons Term.hole (List.cons Term.hole List.empty)) scrutinee in
    elim_result_err (type_check_elim e Term.hole bool_scope_for_elim_tests local_types empty_locals)

/// The scrutinee's own LOCAL type is `NotBool`, not `Bool` -- `e.inductive`
/// says `Bool`, so the rebuilt expected scrutinee type and the scrutinee's
/// real inferred type structurally disagree and `unify` must reject it.
#[test]
def test_type_check_elim_rejects_scrutinee_type_mismatch : Bool :=
    let scrutinee : Term := Term.var 0 DebugName.unnamed in
    let local_types : List Term := List.cons (named_free_var "NotBool") List.empty in
    let motive : Term := Term.lam binder_anon Term.hole (sort_n 0) in
    let e : Elim := Elim.mk bool_name_for_elim_tests List.empty List.empty List.empty motive
        (List.cons Term.hole (List.cons Term.hole List.empty)) scrutinee in
    elim_result_err (type_check_elim e Term.hole bool_scope_for_elim_tests local_types empty_locals)

/// The motive's body is `Term.hole`, whose own inferred type is `Term.hole`
/// -- not a `Term.sort` -- so `sort_level_of` must fail the motive's
/// codomain check, same as a `PathP` line that isn't a line into a sort.
#[test]
def test_type_check_elim_rejects_non_sort_motive : Bool :=
    let scrutinee : Term := Term.var 0 DebugName.unnamed in
    let local_types : List Term := List.cons (named_free_var "Bool") List.empty in
    let motive : Term := Term.lam binder_anon Term.hole Term.hole in
    let e : Elim := Elim.mk bool_name_for_elim_tests List.empty List.empty List.empty motive
        (List.cons Term.hole (List.cons Term.hole List.empty)) scrutinee in
    elim_result_err (type_check_elim e Term.hole bool_scope_for_elim_tests local_types empty_locals)

/// `Bool` declares two constructors; one minor is one short.
#[test]
def test_type_check_elim_rejects_too_few_minors : Bool :=
    let scrutinee : Term := Term.var 0 DebugName.unnamed in
    let local_types : List Term := List.cons (named_free_var "Bool") List.empty in
    let motive : Term := Term.lam binder_anon Term.hole (sort_n 0) in
    let e : Elim := Elim.mk bool_name_for_elim_tests List.empty List.empty List.empty motive
        (List.cons Term.hole List.empty) scrutinee in
    elim_result_err (type_check_elim e Term.hole bool_scope_for_elim_tests local_types empty_locals)

/// Three minors for `Bool`'s two constructors -- one too many.
#[test]
def test_type_check_elim_rejects_too_many_minors : Bool :=
    let scrutinee : Term := Term.var 0 DebugName.unnamed in
    let local_types : List Term := List.cons (named_free_var "Bool") List.empty in
    let motive : Term := Term.lam binder_anon Term.hole (sort_n 0) in
    let e : Elim := Elim.mk bool_name_for_elim_tests List.empty List.empty List.empty motive
        (List.cons Term.hole (List.cons Term.hole (List.cons Term.hole List.empty))) scrutinee in
    elim_result_err (type_check_elim e Term.hole bool_scope_for_elim_tests local_types empty_locals)

/// A genuinely NON-CONSTANT motive: `fn (s : Shape) => tag (Term.var 2)`,
/// where `tag` is itself a bound function value (`Shape -> Sort 1`, kept
/// deliberately OPAQUE/unresolved beyond that declared type). Each
/// minor's own body applies `tag` to ITS OWN constructor -- `circle`'s
/// minor says `tag (circle r)`, `square`'s says `tag (square r)` -- which
/// only BUILDS at all if `type_check_elim_minor` threads the correctly
/// `term_shift`ed motive through each one. `local_types` is
/// `[Shape, Shape -> Sort 1]` (index 0 the scrutinee's own slot, index 1
/// `tag`'s).
///
/// No swapped-minor mutation control: `type_check_lam_explicit`
/// (`infer.mo`) does not itself `unify` an application-shaped body
/// against the Pi's codomain it is checked against -- `type_check_app`
/// is pure inference, and the explicit-binder arm keeps `expected_type`
/// verbatim as the lambda's type whenever `ret_typ` isn't a hole, with no
/// comparison against what `body` actually inferred to. Confirmed
/// directly: swapping which minor goes with which constructor here still
/// returns `ok`. This is a pre-existing, orthogonal gap (not introduced
/// by this rule, and not fixed by it -- recorded in
/// `core-term-simplification.md`'s R4 section as a flag for R4b, since a
/// derived non-constant motive's minors will usually be application-
/// shaped too) rather than something this pin can catch.
def tag_fn_typ : Term := Term.pi binder_anon Term.hole (sort_n 1)
def dependent_motive_for_elim_tests : Term :=
    Term.lam binder_anon Term.hole (Term.app (Term.var 2 DebugName.unnamed) (Term.var 0 DebugName.unnamed))
def dependent_local_types_for_elim_tests : List Term :=
    List.cons (named_free_var "Shape") (List.cons tag_fn_typ List.empty)
def circle_minor_for_elim_tests : Term :=
    Term.lam binder_anon Term.hole
        (Term.app (Term.var 2 DebugName.unnamed) (Term.app (named_free_var "circle") (Term.var 0 DebugName.unnamed)))
def square_minor_for_elim_tests : Term :=
    Term.lam binder_anon Term.hole
        (Term.app (Term.var 2 DebugName.unnamed) (Term.app (named_free_var "square") (Term.var 0 DebugName.unnamed)))

#[test]
def test_type_check_elim_accepts_a_real_dependent_motive : Bool :=
    let scrutinee : Term := Term.var 0 DebugName.unnamed in
    let e : Elim := Elim.mk shape_name_for_elim_tests List.empty List.empty List.empty
        dependent_motive_for_elim_tests
        (List.cons circle_minor_for_elim_tests (List.cons square_minor_for_elim_tests List.empty))
        scrutinee in
    elim_result_ok (type_check_elim e Term.hole shape_scope_for_elim_tests
        dependent_local_types_for_elim_tests empty_locals)

// ─── R4b: motive derivation (core-term-simplification.md) ───────────────
//
// `Sigma.snd`'s own shape (`sigma-types.md`): a scrutinee `p` whose
// DECLARED expected type (`B (Sigma.fst p)`) mentions `p` through a real,
// resolvable projection -- unlike the `Shape`/`tag` pin above, which is
// handed an already-correct motive by hand, this one calls `derive_motive`
// itself and then proves the result actually lets `type_check_elim` accept
// the one minor Sigma.snd's real body has (`fn a b => b`). `MySigma.fst`
// needs a REAL body (not a bare free reference) for this to mean anything:
// checking the minor's inferred type (`B a`) against the motive applied to
// the constructor (`B (MySigma.fst (dpair a b))`) only converts to the same
// term once `MySigma.fst` delta/iota-unfolds -- exactly the `Sigma.fst`
// reduction `sigma-types.md` names as the OTHER prerequisite `Sigma.snd`
// needs, already real and unrelated to this step. Built from real parsed
// source (`try_parse_decls`/`build_scope_from_decls`, `elim_props.mo`'s own
// technique) rather than hand-built `Inductive`/`Param`, so the dependent
// field (`snd : B fst`) and `MySigma.fst`'s `match`-iota both go through
// the real parser/checker instead of a hand-derived de Bruijn guess.
//
// `MySigma`'s own two type ARGUMENTS (as opposed to its declared params)
// must be REAL, resolvable names -- `P`/`Fam` below, not bare free-
// dangling stand-ins the way `pair_scrutinee_typ` gets away with "T"/"U".
// `pair_scrutinee_typ` is only ever UNIFIED against (structural comparison
// alone), never independently type-checked as a term; this pin's motive
// wraps `my_sigma_scrutinee_typ` as a `Term.lam`'s DOMAIN, which
// `type_check_elim_motive` DOES infer/check as a real type -- confirmed by
// running it: an unresolved "A"/"B" fails there with `unknown_var`, caught
// before trusting this pin at all.
def my_sigma_mod_path : ModulePath := ModulePath.mk [Identifier.id "my_sigma_r4b"]

def my_sigma_scope : Scope :=
    let source : String :=
        "type P { p0 }\ndef Fam (x : P) : Type := P\ntype MySigma (A : Type) (B : A -> Type) { dpair (fst : A) (snd : B fst) }\ndef MySigma.fst {A : Type} {B : A -> Type} (p : MySigma A B) : A := match p { dpair a _ => a }" in
    let sd : ScopeData := match try_parse_decls source {
        Option.some decl_list => build_scope_from_decls my_sigma_mod_path decl_list,
        Option.none => build_scope_from_decls my_sigma_mod_path List.empty,
    } in
    {
        module_id := my_sigma_mod_path,
        scope := sd,
        parent := Option.none,
        incomplete_match_ok := false,
    }

/// `MySigma P Fam` -- `P` a real nullary type, `Fam` a real (constant)
/// type family over it, both declared in `my_sigma_scope`'s own source.
def my_sigma_scrutinee_typ : Term :=
    Term.app (Term.app (named_free_var "MySigma") (named_free_var "P")) (named_free_var "Fam")

def my_sigma_local_types : List Term := List.cons my_sigma_scrutinee_typ List.empty

/// `p`, the scrutinee -- the def's own (only) bound parameter, index 0.
def my_sigma_p : Term := Term.var 0 DebugName.unnamed

/// `Fam (MySigma.fst p)` -- `Sigma.snd`'s own declared return type,
/// verbatim shape (`B (Sigma.fst p)` with `B := Fam`).
def my_sigma_expected_type : Term :=
    Term.app (named_free_var "Fam") (Term.app (named_free_var "MySigma.fst") my_sigma_p)

/// `[P, Fam]` -- `MySigma`'s own two type arguments, read off the
/// scrutinee type's application spine the same way `Elim.params` always
/// does (R3b/R4's own convention).
def my_sigma_params : List Term :=
    List.cons (named_free_var "P") (List.cons (named_free_var "Fam") List.empty)

/// `fn a b => b` -- `Sigma.snd`'s own body (`match p { dpair a b => b }`),
/// curried the way `type_check_elim_minor`'s own Pi-chain expects a minor
/// (one `Term.lam` per field, outermost-first).
def my_sigma_snd_minor : Term :=
    Term.lam binder_anon Term.hole (Term.lam binder_anon Term.hole (Term.var 0 DebugName.unnamed))

#[test]
def test_derive_motive_lets_sigma_snd_shaped_elim_check : Bool :=
    let motive : Term := derive_motive 0 my_sigma_scrutinee_typ my_sigma_expected_type in
    let e : Elim := Elim.mk (NamePath.mk [Identifier.id "MySigma"]) List.empty my_sigma_params List.empty
        motive (List.cons my_sigma_snd_minor List.empty) my_sigma_p in
    elim_result_ok (type_check_elim e Term.hole my_sigma_scope my_sigma_local_types empty_locals)

/// No swapped/wrong-motive mutation control here -- confirmed directly,
/// and worth recording rather than silently dropping: a motive that does
/// NOT abstract `p` at all (`Term.lam binder_anon my_sigma_scrutinee_typ
/// (term_shift 1 my_sigma_expected_type)`, verbatim-wrapping the original
/// expected type under a binder it never references) is STILL ACCEPTED
/// here. Root cause is the same class of gap `test_type_check_elim_
/// accepts_a_real_dependent_motive`'s own doc comment already names for
/// an application-shaped minor body, now confirmed for a bound-variable
/// one too: `type_check_bound_var` (`infer.mo`) returns `local_types`'s
/// entry for the variable and NEVER consults (let alone `unify`s against)
/// the `expected_type` it is handed -- `Sigma.snd`'s own real body
/// (`match p { dpair a b => b }`) is EXACTLY a minor whose tail is a bare
/// bound variable (`b`), so this is not an edge case for R4b, it is the
/// motivating one. `derive_motive`'s own correctness is instead
/// mutation-verified one level down, directly on `term_abstract_var`
/// (`subst.mo`'s own pins) -- those DO catch a wrong abstraction, since
/// they inspect the produced term's shape directly rather than routing it
/// through this unchecked path. Recorded here, not fixed: widening
/// `type_check_bound_var`/`type_check_app` to a real bidirectional check
/// is its own, separately-scoped change with its own blast radius across
/// the whole checker, not something R4b's own scope covers.

// ─── R4c: index abstraction (core-term-simplification.md) ───────────────
//
// `Eq.rec`'s own shape (`init/src/prelude.mo`): a motive over BOTH the
// index (`b`) and the scrutinee (`e`), `(b : A) -> Eq A a b -> Sort 1` --
// one argument more than R4/R4b's own pins ever needed. `MyEq`/`P` mirror
// the real `Eq`/`Bool`-style fixtures elsewhere in this file, built from
// real parsed source (same `try_parse_decls` technique as R4b's
// `MySigma`) so `MyEq.refl`'s own declared return type (`MyEq A a a`) is
// the REAL, parser-kept term `ctor_index_values` reads, not a hand-
// guessed one. `P` has TWO constructors (`p0`/`p1`), not one, so a
// caller's own generic index (`p1`, standing for `Eq.rec`'s `b`) is
// DIFFERENT from what `refl`'s own return type actually specializes it to
// (`p0`, matching `a`) -- the one shape that actually exercises `ctor_
// index_values` computing a PER-CONSTRUCTOR value rather than echoing the
// caller's own `indices` back unchanged.
def my_eq_mod_path : ModulePath := ModulePath.mk [Identifier.id "my_eq_r4c"]

def my_eq_scope : Scope :=
    let source : String :=
        "type P { p0, p1 }\ntype Marker1 { m1 }\ntype Marker2 { m2 }\ndef Fam (x : P) : Type := match x { p0 => Marker1, p1 => Marker2 }\ntype MyEq (A : Type) (a : A) (b : A) { refl : MyEq A a a }" in
    let sd : ScopeData := match try_parse_decls source {
        Option.some decl_list => build_scope_from_decls my_eq_mod_path decl_list,
        Option.none => build_scope_from_decls my_eq_mod_path List.empty,
    } in
    {
        module_id := my_eq_mod_path,
        scope := sd,
        parent := Option.none,
        incomplete_match_ok := false,
    }

/// `[P, P.p0]` -- `MyEq`'s own first two type arguments (`A := P`, `a :=
/// P.p0`), the "fixed" half of the instantiation.
def my_eq_params : List Term :=
    List.cons (named_free_var "P") (List.cons (named_free_var "P.p0") List.empty)

/// `[P.p1]` -- the caller's own GENERIC index value (`Eq.rec`'s `b`),
/// deliberately DIFFERENT from what `refl`'s own return type specializes
/// to (`P.p0`) -- the whole point of this fixture.
def my_eq_indices : List Term := List.cons (named_free_var "P.p1") List.empty

/// `MyEq P p0 p1` -- the scrutinee's own claimed type, `params ++
/// indices` applied to `MyEq`, matching how `e : Eq A a b` (`b` ARBITRARY,
/// not forced to equal `a`) is `Eq.rec`'s own real parameter.
def my_eq_scrutinee_typ : Term :=
    Term.app (Term.app (Term.app (named_free_var "MyEq") (named_free_var "P"))
        (named_free_var "P.p0")) (named_free_var "P.p1")

def my_eq_local_types : List Term := List.cons my_eq_scrutinee_typ List.empty

/// `e`, the scrutinee -- the def's own (only) bound parameter, index 0.
def my_eq_e : Term := Term.var 0 DebugName.unnamed

/// `(x : P) -> MyEq P p0 x -> Type` by inference -- `Fam x`'s own result
/// type (`Type`) is what makes the motive's CODOMAIN a sort once both
/// `Pi`s are peeled; `Fam x` itself (the BODY) is what makes each minor's
/// expected type depend on the INDEX the checker computes for that
/// constructor, which is the thing under test.
def my_eq_motive : Term :=
    Term.lam binder_anon (named_free_var "P")
        (Term.lam binder_anon my_eq_scrutinee_typ_at_x (Term.app (named_free_var "Fam") (Term.var 1 DebugName.unnamed)))

/// `MyEq P p0 x`, where `x` is the just-introduced index binder (de Bruijn
/// 0 at this position, under the motive's own first `Pi`) -- the
/// scrutinee-Pi's own domain, generalizing `my_eq_scrutinee_typ`'s fixed
/// `p1` to the bound `x`.
def my_eq_scrutinee_typ_at_x : Term :=
    Term.app (Term.app (Term.app (named_free_var "MyEq") (named_free_var "P"))
        (named_free_var "P.p0")) (Term.var 0 DebugName.unnamed)

/// `refl`'s own minor: zero fields, so its body is checked DIRECTLY
/// (no lambda chain) against `motive <refl's own computed index> (refl)`,
/// intended as `Fam P.p0 = Marker1` (the correct computation) vs `Fam
/// P.p1 = Marker2` (the caller's generic index, wrongly reused).
///
/// **This pin alone cannot mutation-discriminate the two -- confirmed
/// directly, not assumed.** Mutating `ctor_index_values` to just echo the
/// caller's generic indices back (`drop_n num_params actual_args`,
/// skipping `ctor.typ` entirely) makes this SAME pin still pass with
/// EITHER `Marker1` or `Marker2` as the minor. Root cause, found by
/// tracing it rather than guessing: `type_check_free_var` (`infer.mo`),
/// like `type_check_bound_var` (R4b's own finding 5), does not `unify`
/// the resolved name's real type against the `expected_type` it is
/// handed for an ordinary (non-constrained) reference like `Marker1` --
/// so a `Term.var` reference of EITHER kind, bound or free, passes
/// against any application-shaped expected type a minor's own tail
/// position hands it. This generalizes R4b's finding 5 from "bound
/// variables" to "`Term.var` in general." The real mutation-checked
/// negative control is `test_ctor_index_values_computes_refl_own_
/// specialization` below, which inspects `ctor_index_values`'s OWN
/// output directly rather than routing through this unchecked path --
/// confirmed BY mutating `ctor_index_values` the same way and rerunning:
/// that pin fails, this one doesn't. Kept anyway as the real plumbing/
/// capstone proof (the whole `Eq.rec`-shaped `Elim` -- motive, two
/// index Pis, the one minor -- does check end to end with a CORRECT
/// answer), exactly how R4b's own integration pin is kept for the same
/// reason.
def my_eq_refl_minor : Term := named_free_var "Marker1"

#[test]
def test_type_check_elim_computes_per_constructor_index_not_the_callers_generic_one : Bool :=
    let e : Elim := Elim.mk (NamePath.mk [Identifier.id "MyEq"]) List.empty my_eq_params my_eq_indices
        my_eq_motive (List.cons my_eq_refl_minor List.empty) my_eq_e in
    elim_result_ok (type_check_elim e Term.hole my_eq_scope my_eq_local_types empty_locals)

/// The REAL mutation-checked negative control (see the doc comment
/// above) -- a direct unit pin on `ctor_index_values` itself: resolves
/// `MyEq`'s real `refl` constructor from `my_eq_scope` and confirms its
/// own computed index is `P.p0`, not the caller's generic `P.p1`
/// (`my_eq_indices`) and not `Term.hole`/anything else that could pass by
/// accident.
def refl_ctor_of (ind : Inductive) : Option InductConstructor :=
    match ind.constructors {
        List.cons refl_ctor rest =>
            if List.is_empty rest then Option.some refl_ctor else Option.none,
        List.empty => Option.none,
    }

def only_index_is_p0 (vals : List Term) : Bool :=
    match vals {
        List.cons only rest =>
            if List.is_empty rest then term_is_named_var only "P.p0" else false,
        List.empty => false,
    }

#[test]
def test_ctor_index_values_computes_refl_own_specialization : Bool :=
    match scope_find_inductive (NamePath.mk [Identifier.id "MyEq"]) my_eq_scope {
        Result.err _ => false,
        Result.ok ind =>
            match refl_ctor_of ind {
                Option.none => false,
                Option.some refl_ctor =>
                    let actual_args : List Term := List.append my_eq_params my_eq_indices in
                    only_index_is_p0 (ctor_index_values ind actual_args (List.length my_eq_params) refl_ctor),
            },
    }
