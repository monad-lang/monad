use lang.types {
  Con, DebugName, Identifier, Inductive, Instance, InstanceKey, Literal,
  LocalScope, LocalVar, MatchCase, ModulePath, NameRef, Native, Param, Scope,
  ScopeClassDef, ScopeDef, ScopeError, Similar, Term, TypeConstraint, TypeError,
  app, con, custom, forall, hole, id, if_, lam, list_rev_loop, list_reverse, lit,
  many, match_, mc, mk, mp, name, named, nid, not_a_type, ntv, num, pi, str,
  type_, unknown_var, unnamed, var,
}
open types {}
use lang.scope {
  inductive_has_constructor, scope_find_class_def_by_name, scope_find_inductive,
  scope_find_inductive_by_constructor, scope_push_local, scope_resolve_instance,
  scope_resolve_name,
}
use lang.typecheck.unify {unify}

/// A type-checked term paired with its type.
struct TypedTerm {
    term : Term,
    typ : Term,
}

/// A type-checked match case with inferred body type.
struct CheckedCase {
    case_ : MatchCase,
    body_typ_ : Term,
}

/// Accumulator for processing match cases: the unified body
/// type and the checked cases in reverse order.
struct CaseAcc {
    body_typ : Term,
    cases : List MatchCase,
}

/// Free variable sentinel from parser (matches elaborate.mo).
def sentinel : I64 := -1

/// Empty local scope (no local bindings).
def empty_locals : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

/// Empty list of local types (no de Bruijn bindings).
def empty_local_types : List Term := List.empty

/// Type check a term bidirectionally.
def type_check (term : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match term {
        Term.lit value => type_check_lit value expected_type scope local_types locals,
        Term.var idx dbg => type_check_var idx dbg expected_type scope local_types locals,
        Term.lam dbg t body => type_check_lam dbg t body expected_type scope local_types locals,
        Term.app f a => type_check_app f a expected_type scope local_types locals,
        Term.forall dbg kind body => type_check_forall dbg kind body scope local_types locals,
        Term.pi arg ret => type_check_pi arg ret scope local_types locals,
        Term.con c => type_check_con c expected_type scope local_types locals,
        Term.ntv ntv => type_check_ntv ntv expected_type scope local_types locals,
        Term.type_ level => type_check_sort_full level expected_type,
        Term.hole => ok ({ term := expected_type, typ := expected_type }),
    }

/// Build a TypedTerm from term and type.
def mk_typed (a : Term) (b : Term) : TypedTerm :=
    { term := a, typ := b }

/// Get the term field from a TypedTerm.
def tt_term (tt : TypedTerm) : Term :=
    match tt { mk term _ => term }

/// Get the type field from a TypedTerm.
def tt_typ (tt : TypedTerm) : Term :=
    match tt { mk _ typ => typ }

// --- Instance resolution helpers ---

/// Derive an instance key from a class class_def and an expected type.
/// The expected type should be the type at which the class method is being used.
def derive_instance_key (class_def : Inductive) (class_method : ScopeClassDef) (expected_type : Term) : Result TypeError InstanceKey :=
    // For now, this is a stub. The full implementation would:
    // 1. Match expected_type against the class parameters
    // 2. Extract the type arguments
    // 3. Build an InstanceKey with those args
    // For simplicity, we'll just return a basic key with empty args
    // This needs to be implemented properly for full instance resolution
    match class_method {
        mk class_name _full_name _name _sig =>
            let empty_args : List Param := List.empty in
            let empty_constraints : List TypeConstraint := List.empty in
            ok ({ cls := class_name, constraints := empty_constraints, args := empty_args })
    }

/// Resolve a class method reference to a concrete instance method.
/// Looks up the instance in the scope and returns the concrete method definition.
def resolve_class_method (class_method : ScopeClassDef) (expected_type : Term) (scope : Scope) : Result TypeError ScopeDef :=
    // Extract class_name via pattern matching (struct field access via dot syntax not supported)
    match class_method {
        mk class_name full_name method_name sig =>
            // Derive the instance key from the expected type
            let class_find : Result ScopeError Inductive := scope_find_inductive class_name scope in
            match class_find {
                ok class_def =>
                    let key_result : Result TypeError InstanceKey := derive_instance_key class_def class_method expected_type in
                    match key_result {
                        ok key =>
                            let inst_result : Result ScopeError Instance := scope_resolve_instance class_name key scope in
                            match inst_result {
                                ok inst =>
                                    // For now, instance methods are not stored in the self-hosted version
                                    // Fall back to the class method signature
                                    // TODO: When Instance has impls_map, look up the concrete method
                                    // Return the class method signature as a fallback
                                    let empty_mp : ModulePath := ModulePath.mp List.empty in
                                    ok ({ name := full_name, module := empty_mp, sig := sig, body := Term.hole }),
                                err _ => err (TypeError.custom "Instance not found"),
                            },
                        err e => err e,
                    },
                err _ => err (TypeError.custom "Class not found"),
            }
    }

/// Type check a literal value.
def type_check_lit (value : Literal) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match value {
        Literal.str s =>
            ok (mk_typed (Term.lit value) (Term.type_ 1)),
        Literal.num n suffix =>
            ok (mk_typed (Term.lit value) (Term.type_ 1)),
        Literal.if_ one two three =>
            type_check_if one two three expected_type scope local_types locals,
        Literal.match_ value_ cases =>
            type_check_match value_ cases expected_type scope local_types locals,
    }

/// Type check an if expression.
def type_check_if (one : Term) (two : Term) (three : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    let bool_typ : Term := Term.type_ 1 in
    match type_check one bool_typ scope local_types locals {
        ok cond_tt =>
            let cond_term : Term := tt_term cond_tt in
            match type_check two expected_type scope local_types locals {
                ok then_tt =>
                    let then_term : Term := tt_term then_tt in
                    let then_typ : Term := tt_typ then_tt in
                    match type_check three then_typ scope local_types locals {
                        ok els_tt =>
                            let els_term : Term := tt_term els_tt in
                            let lit_val : Literal := Literal.if_ cond_term then_term els_term in
                            ok (mk_typed (Term.lit lit_val) then_typ),
                        err e => err e,
                    },
                err e => err e,
            },
        err e => err e,
    }

/// Type check a match expression.
#[terminating]
def type_check_match (value_ : Term) (cases : List MatchCase) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match type_check value_ Term.hole scope local_types locals {
        ok sc_tt =>
            let sc_term : Term := tt_term sc_tt in
            let sc_typ : Term := tt_typ sc_tt in
            match validate_match_constructors cases scope {
                err e => err e,
                ok _ => type_check_cases cases sc_term sc_typ expected_type scope local_types locals,
            },
        err e => err e,
    }

/// Validate that all non-wildcard case constructors belong to the same inductive.
/// Returns ok if valid or if no inductive found (skip validation).
def validate_match_constructors (cases : List MatchCase) (scope : Scope) : Result TypeError Bool :=
    match find_inductive_for_cases cases scope {
        Option.none => ok true,
        Option.some ind =>
            validate_cases_against_inductive cases ind,
    }

/// Find the inductive that the first non-wildcard case constructor belongs to.
def find_inductive_for_cases (cases : List MatchCase) (scope : Scope) : Option Inductive :=
    match cases {
        List.empty => Option.none,
        List.cons hd rest =>
            match hd {
                MatchCase.mc name _ _ =>
                    let wildcard_id : Identifier := Identifier.id "_" in
                    if Similar.similar name wildcard_id
                    then find_inductive_for_cases rest scope
                    else
                        let con_mp : ModulePath := ModulePath.mp (List.cons name List.empty) in
                        scope_find_inductive_by_constructor con_mp scope,
            },
    }

/// Check that every non-wildcard case constructor exists in the inductive.
def validate_cases_against_inductive (cases : List MatchCase) (ind : Inductive) : Result TypeError Bool :=
    match cases {
        List.empty => ok true,
        List.cons hd rest =>
            match hd {
                MatchCase.mc name _ _ =>
                    let wildcard_id : Identifier := Identifier.id "_" in
                    if Similar.similar name wildcard_id
                    then validate_cases_against_inductive rest ind
                    else
                        let con_mp : ModulePath := ModulePath.mp (List.cons name List.empty) in
                        if inductive_has_constructor ind con_mp
                        then validate_cases_against_inductive rest ind
                        else err (TypeError.custom "constructor not found in inductive"),
            },
    }

/// Type check match cases — process all cases and unify their body types.
def type_check_cases (cases : List MatchCase) (scrutinee_term : Term) (scrutinee_typ : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match type_check_cases_accum cases scrutinee_term scrutinee_typ scope local_types locals (Term.hole) List.empty {
        ok acc =>
            match acc {
                mk body_typ checked_cases =>
                    match unify body_typ expected_type {
                        ok unified_typ =>
                            let lit_val : Literal := Literal.match_ scrutinee_term checked_cases in
                            ok (mk_typed (Term.lit lit_val) unified_typ),
                        err e => err e,
                    },
            },
        err e => err e,
    }

/// Recursively type-check each case, accumulating checked cases and a
/// progressively unified body type. `acc_cases` is built in reverse order
/// and reversed at the end.
#[terminating]
def type_check_cases_accum (cases : List MatchCase) (scrutinee_term : Term) (scrutinee_typ : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) (acc_typ : Term) (acc_cases : List MatchCase) : Result TypeError CaseAcc :=
    match cases {
        List.cons hd rest =>
            match type_check_match_case hd scrutinee_term scrutinee_typ scope local_types locals {
                ok checked =>
                    match checked {
                        mk checked_case body_typ =>
                            let new_cases : List MatchCase := List.cons checked_case acc_cases in
                            match acc_typ {
                                Term.hole =>
                                    type_check_cases_accum rest scrutinee_term scrutinee_typ scope local_types locals body_typ new_cases,
                                _ =>
                                    match unify acc_typ body_typ {
                                        ok unified_typ =>
                                            type_check_cases_accum rest scrutinee_term scrutinee_typ scope local_types locals unified_typ new_cases,
                                        err e => err e,
                                    },
                            },
                    },
                err e => err e,
            },
        List.empty =>
            let reversed : List MatchCase := list_reverse acc_cases in
            ok ({ body_typ := acc_typ, cases := reversed }),
    }

/// List reverse helper.
#[terminating]
def list_reverse {A : Type} (xs : List A) : List A :=
    list_rev_loop xs List.empty

#[terminating]
def list_rev_loop {A : Type} (xs : List A) (acc : List A) : List A :=
    match xs {
        List.cons x rest => list_rev_loop rest (List.cons x acc),
        List.empty => acc,
    }

/// Type check a single match case arm.
def type_check_match_case (case_ : MatchCase) (scrutinee_term : Term) (scrutinee_typ : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError CheckedCase :=
    match case_ {
        MatchCase.mc name args body =>
            let wildcard_id : Identifier := Identifier.id "_" in
            if Similar.similar name wildcard_id then
                match args {
                    List.empty =>
                        type_check_case_body_checked name args body scope local_types locals,
                    _ =>
                        err (TypeError.custom "wildcard pattern cannot bind arguments"),
                }
            else
                match args {
                    List.empty =>
                        type_check_case_body_checked name args body scope local_types locals,
                    _ =>
                        let extended_types : List Term := prepend_holes args local_types in
                        let extended_locals : LocalScope := prepend_local_vars args locals in
                        type_check_case_body_checked name args body scope extended_types extended_locals,
                },
    }

/// Prepend a Term.hole for each identifier onto the front of local_types.
def prepend_holes (args : List Identifier) (local_types : List Term) : List Term :=
    match args {
        List.cons x rest => prepend_holes rest (List.cons Term.hole local_types),
        List.empty => local_types,
    }

/// Prepend LocalVar bindings (with Term.hole type, Multiplicity.many) for each identifier onto locals.
def prepend_local_vars (args : List Identifier) (locals : LocalScope) : LocalScope :=
    let new_vars : List LocalVar := rec_prepend_local_vars args in
    { vars := new_vars, parent := Option.some locals }

/// Recursively build a list of LocalVar entries from identifiers.
def rec_prepend_local_vars (args : List Identifier) : List LocalVar :=
    match args {
        List.cons x rest =>
            let lv : LocalVar := { name := x, typ := Term.hole, multiplicity := Multiplicity.many } in
            List.cons lv (rec_prepend_local_vars rest),
        List.empty => List.empty,
    }

/// Type-check the body of a match case arm, returning the checked result.
def type_check_case_body_checked (name : Identifier) (args : List Identifier) (body : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError CheckedCase :=
    match type_check body Term.hole scope local_types locals {
        ok body_tt =>
            let body_term : Term := tt_term body_tt in
            let body_typ : Term := tt_typ body_tt in
            let new_case : MatchCase := MatchCase.mc name args body_term in
            ok ({ case_ := new_case, body_typ_ := body_typ }),
        err e => err e,
    }

/// Type check a variable reference.
def type_check_var (idx : I64) (dbg : DebugName) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    if I64.beq idx sentinel then
        type_check_free_var dbg expected_type scope locals
    else
        type_check_bound_var idx dbg local_types

/// Look up a free variable by debug name in the scope.
def type_check_free_var (dbg : DebugName) (expected_type : Term) (scope : Scope) (locals : LocalScope) : Result TypeError TypedTerm :=
    match dbg {
        DebugName.named id =>
            let nref : NameRef := NameRef.nid id in
            let result : Result ScopeError ScopeDef := scope_resolve_name nref scope locals in
            match result {
                ok sd => match sd {
                    mk _ _ sig _ =>
                        ok (mk_typed (Term.var sentinel dbg) sig),
                },
                err _ =>
                    let clsd_result : Result ScopeError ScopeClassDef := scope_find_class_def_by_name id scope in
                    match clsd_result {
                        ok cd =>
                            // Try to resolve class method to concrete instance
                            match resolve_class_method cd expected_type scope {
                                ok instance_def =>
                                    match instance_def {
                                        mk _ _ inst_sig _ =>
                                            ok (mk_typed (Term.var sentinel dbg) inst_sig),
                                    },
                                err _ =>
                                    // Fall back to class method signature (not resolved)
                                    match cd {
                                        mk _class_name _full_name _ sig =>
                                            ok (mk_typed (Term.var sentinel dbg) sig),
                                    },
                            },
                        err _ =>
                            err (TypeError.unknown_var nref),
                    },
            },
        DebugName.unnamed =>
            ok (mk_typed (Term.var sentinel dbg) (Term.type_ 1)),
    }

/// Look up a bound variable by de Bruijn index.
def type_check_bound_var (idx : I64) (dbg : DebugName) (local_types : List Term) : Result TypeError TypedTerm :=
    match nth_type idx local_types {
        Option.some typ =>
            ok (mk_typed (Term.var idx dbg) typ),
        Option.none =>
            let bogus_id : Identifier := Identifier.id "bound_var" in
            err (TypeError.unknown_var (NameRef.nid bogus_id)),
    }

/// Get the nth element from a list (0-indexed).
def nth_type (idx : I64) (types : List Term) : Option Term :=
    if I64.beq idx 0 then
        match types {
            List.cons hd _ => Option.some hd,
            List.empty => Option.none,
        }
    else
        match types {
            List.cons _ rest => nth_type (idx - 1) rest,
            List.empty => Option.none,
        }

/// Type check a lambda expression.
def type_check_lam (dbg : DebugName) (t : Term) (body : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match expected_type {
        Term.pi arg_typ ret_typ =>
            let extended_types : List Term := List.cons arg_typ local_types in
            let lv : LocalVar := {
                name := debug_name_to_id dbg,
                typ := arg_typ,
                multiplicity := Multiplicity.many,
            } in
            let extended_locals : LocalScope := scope_push_local lv locals in
            match type_check body ret_typ scope extended_types extended_locals {
                ok body_tt =>
                    let checked_body : Term := tt_term body_tt in
                    let lam_term : Term := Term.lam dbg arg_typ checked_body in
                    ok (mk_typed lam_term expected_type),
                err e => err e,
            },
        _ =>
            match type_check t Term.hole scope local_types locals {
                ok t_tt =>
                    let inferred_typ : Term := tt_typ t_tt in
                    let extended_types : List Term := List.cons t local_types in
                    let lv : LocalVar := {
                        name := debug_name_to_id dbg,
                        typ := t,
                        multiplicity := Multiplicity.many,
                    } in
                    let extended_locals : LocalScope := scope_push_local lv locals in
                    match type_check body Term.hole scope extended_types extended_locals {
                        ok body_tt =>
                            let checked_body : Term := tt_term body_tt in
                            let body_typ : Term := tt_typ body_tt in
                            let pi_typ : Term := Term.pi t body_typ in
                            let lam_term : Term := Term.lam dbg t checked_body in
                            ok (mk_typed lam_term pi_typ),
                        err e => err e,
                    },
                err e => err e,
            },
    }

/// Extract an identifier from a DebugName (for scope registration).
def debug_name_to_id (dbg : DebugName) : Identifier :=
    match dbg {
        DebugName.named id => id,
        DebugName.unnamed => Identifier.id "_",
    }

/// Type check a function application.
def type_check_app (f : Term) (a : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match type_check a Term.hole scope local_types locals {
        ok a_tt =>
            let a_term : Term := tt_term a_tt in
            let a_typ : Term := tt_typ a_tt in
            let f_expected : Term := Term.pi a_typ expected_type in
            match type_check f f_expected scope local_types locals {
                ok f_tt =>
                    let f_term : Term := tt_term f_tt in
                    let f_typ : Term := tt_typ f_tt in
                    extract_pi_ret f_term a_term f_typ a_typ expected_type scope local_types locals,
                err e => err e,
            },
        err e => err e,
    }

/// Extract the return type from the function's type after application.
def extract_pi_ret (f_term : Term) (a_term : Term) (f_typ : Term) (a_typ : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match f_typ {
        Term.pi pi_arg pi_ret =>
            let app_term : Term := Term.app f_term a_term in
            ok (mk_typed app_term pi_ret),
        Term.forall _ _ body_ =>
            extract_pi_ret f_term a_term body_ a_typ expected_type scope local_types locals,
        _ =>
            let app_term : Term := Term.app f_term a_term in
            ok (mk_typed app_term expected_type),
    }

/// Type check a forall binder.
def type_check_forall (dbg : DebugName) (kind : Term) (body : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match type_check kind Term.hole scope local_types locals {
        ok _ =>
            let extended_types : List Term := List.cons kind local_types in
            match type_check body Term.hole scope extended_types locals {
                ok _ =>
                    let forall_term : Term := Term.forall dbg kind body in
                    ok (mk_typed forall_term (Term.type_ 1)),
                err e => err e,
            },
        err e => err e,
    }

/// Type check a Pi type.
def type_check_pi (arg : Term) (ret : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match type_check arg Term.hole scope local_types locals {
        ok _ =>
            let extended_types : List Term := List.cons arg local_types in
            match type_check ret Term.hole scope extended_types locals {
                ok _ =>
                    let pi_term : Term := Term.pi arg ret in
                    ok (mk_typed pi_term (Term.type_ 1)),
                err e => err e,
            },
        err e => err e,
    }

/// Type check a sort universe level.
def type_check_sort_full (level : I64) (expected_type : Term) : Result TypeError TypedTerm :=
    match expected_type {
        Term.hole =>
            let sort_term : Term := Term.type_ level in
            ok (mk_typed sort_term (Term.type_ (level + 1))),
        Term.type_ expected_level =>
            let sort_term : Term := Term.type_ level in
            if I64.beq expected_level level then
                ok (mk_typed sort_term expected_type)
            else if expected_level > level then
                ok (mk_typed sort_term expected_type)
            else
                err (TypeError.not_a_type sort_term),
        _ =>
            let sort_term : Term := Term.type_ level in
            err (TypeError.not_a_type sort_term),
    }

/// Type check a constructor application.
def type_check_con (c : Con) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    ok (mk_typed (Term.con c) expected_type)

/// Type check a native term.
def type_check_ntv (n : Native) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    ok (mk_typed (Term.ntv n) expected_type)
