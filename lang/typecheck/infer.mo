use lang.types
open types
use lang.scope

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
        Term.ntv ntv => type_check_ntv ntv expected_type,
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
@[terminating]
def type_check_match (value_ : Term) (cases : List MatchCase) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match type_check value_ Term.hole scope local_types locals {
        ok sc_tt =>
            let sc_term : Term := tt_term sc_tt in
            let sc_typ : Term := tt_typ sc_tt in
            type_check_cases cases sc_term sc_typ expected_type scope local_types locals,
        err e => err e,
    }

/// Type check match cases.
def type_check_cases (cases : List MatchCase) (scrutinee_term : Term) (scrutinee_typ : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match cases {
        List.cons hd rest =>
            match type_check_match_case hd scrutinee_term scrutinee_typ scope local_types locals {
                ok checked =>
                    match checked {
                        mk checked_case case_body_typ =>
                            let lit_val : Literal := Literal.match_ scrutinee_term (List.cons checked_case List.empty) in
                            ok (mk_typed (Term.lit lit_val) case_body_typ),
                    },
                err e => err e,
            },
        List.empty =>
            let lit_val : Literal := Literal.match_ scrutinee_term List.empty in
            ok (mk_typed (Term.lit lit_val) expected_type),
    }

/// Type check a single match case arm.
def type_check_match_case (case_ : MatchCase) (scrutinee_term : Term) (scrutinee_typ : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError CheckedCase :=
    match case_ {
        MatchCase.mc name args body =>
            match type_check body Term.hole scope local_types locals {
                ok body_tt =>
                    let body_term : Term := tt_term body_tt in
                    let body_typ : Term := tt_typ body_tt in
                    let new_case : MatchCase := MatchCase.mc name args body_term in
                    let result : CheckedCase := { case_ := new_case, body_typ_ := body_typ } in
                    ok result,
                err e => err e,
            },
    }

/// Type check a variable reference.
def type_check_var (idx : I64) (dbg : DebugName) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    if I64.beq idx sentinel then
        type_check_free_var dbg scope locals
    else
        type_check_bound_var idx dbg local_types

/// Look up a free variable by debug name in the scope.
def type_check_free_var (dbg : DebugName) (scope : Scope) (locals : LocalScope) : Result TypeError TypedTerm :=
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
                    err (TypeError.unknown_var nref),
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
def type_check_ntv (n : Native) (expected_type : Term) : Result TypeError TypedTerm :=
    ok (mk_typed (Term.ntv n) expected_type)
