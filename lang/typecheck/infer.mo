use lang.types {
  Con, DebugName, Identifier, Inductive, Instance, InstanceKey, Literal,
  LocalScope, LocalVar, MatchCase, ModulePath, NameRef, Native, Param, Scope,
  ScopeClassDef, ScopeDef, ScopeError, Similar, StructLitField, Term,
  TypeConstraint, TypeError,
  app, con, custom, forall, hole, id, id_eq, if_, lam, list_rev_loop,
  list_reverse, lit, many, match_, mc, mk, mp, name, named, nid, not_a_type,
  ntv, num, pi, show_module_path, str, type_, unknown_constructor,
  unknown_type, unknown_var, unnamed, var,
}
use lang.scope {
  find_constructor_in_inductive, inductive_has_constructor, list_append,
  scope_data_add_inductive, scope_data_empty, scope_find_class_def_by_name,
  scope_find_inductive, scope_find_inductive_by_constructor, scope_push_local,
  scope_resolve_instance, scope_resolve_name,
}
use lang.typecheck.unify {unify}
use std.list {length}

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
        Literal.flt text suffix =>
            ok (mk_typed (Term.lit value) (Term.type_ 1)),
        Literal.if_ one two three =>
            type_check_if one two three expected_type scope local_types locals,
        Literal.match_ value_ cases =>
            type_check_match value_ cases expected_type scope local_types locals,
        Literal.struct_lit fields type_name =>
            type_check_struct_lit fields type_name expected_type scope local_types locals,
        Literal.struct_update base fields =>
            type_check_struct_update base fields expected_type scope local_types locals,
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
            match validate_match_constructors cases sc_typ scope {
                err e => err e,
                ok _ => type_check_cases cases sc_term sc_typ expected_type scope local_types locals,
            },
        err e => err e,
    }

/// Validate that all non-wildcard case constructors belong to the same inductive.
/// Returns ok if valid or if no inductive found (skip validation).
def validate_match_constructors (cases : List MatchCase) (scrutinee_typ : Term) (scope : Scope) : Result TypeError Bool :=
    match find_inductive_for_cases cases scrutinee_typ scope {
        Option.none => ok true,
        Option.some ind =>
            validate_cases_against_inductive cases ind,
    }

/// Unwrap a `Term.app f a` chain down to its head, returning the
/// `Identifier` if that head is a named free/global variable (`Term.var
/// _ (DebugName.named id)`) -- covers both a bare type reference
/// (`List`) and an applied generic (`List Identifier`). `Option.none`
/// for anything else (`Term.hole`, a bound/unnamed var, ...) -- those
/// cases fall back to `find_inductive_for_cases_by_constructor` below.
def type_head_name (t : Term) : Option Identifier :=
    match t {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => Option.some id,
                DebugName.unnamed => Option.none,
            },
        Term.app f _ => type_head_name f,
        _ => Option.none,
    }

/// Find the inductive a match's cases belong to. Prefers an exact
/// lookup by the scrutinee's own inferred type name when one is known
/// (`scope_find_inductive`, unambiguous by construction -- type names
/// don't collide the way constructor names do) -- falls back to
/// scanning by the first non-wildcard case's constructor name only
/// when the scrutinee's type isn't concretely known (`Term.hole`, a
/// generic type parameter, a lookup-by-name miss, ...), preserving
/// this function's previous (still real, still sometimes needed)
/// behavior exactly. The constructor-name scan alone is ambiguous
/// whenever two inductives share a constructor name -- confirmed live:
/// `init/prelude.mo` declares both `List` (`cons`/`empty`) and `Vec` (a
/// length-indexed GADT-style type, also `cons`), so validating a plain
/// `match x { List.cons hd rest => ..., List.empty => ... }` could pick
/// `Vec` depending on scan order and then fail ("`Vec` has no
/// `empty`") -- this was the single largest remaining blocker in
/// `lang/codegen/emit.mo`'s corpus check. A scan-order-only fix
/// ("prefer first-declared") was tried and reverted: it fixed this one
/// collision but regressed a DIFFERENT one once more of the corpus
/// started passing (measured: emit.mo's error count went 14 -> 44) --
/// see `plans/bootstrapping/self-hosted-compiler.md`'s changelog. This
/// version instead only ever ADDS a strictly-better preferred path and
/// never changes the shared fallback's behavior, so it can't regress
/// any case that previously worked.
def find_inductive_for_cases (cases : List MatchCase) (scrutinee_typ : Term) (scope : Scope) : Option Inductive :=
    match type_head_name scrutinee_typ {
        Option.some id =>
            match scope_find_inductive (ModulePath.mp (List.cons id List.empty)) scope {
                ok ind => Option.some ind,
                err _ => find_inductive_for_cases_by_constructor cases scope,
            },
        Option.none => find_inductive_for_cases_by_constructor cases scope,
    }

/// The original constructor-name-scan lookup, unchanged -- ambiguous
/// when constructor names collide, but still the correct behavior when
/// the scrutinee's own type isn't concretely known (see
/// `find_inductive_for_cases`'s own doc comment above).
def find_inductive_for_cases_by_constructor (cases : List MatchCase) (scope : Scope) : Option Inductive :=
    match cases {
        List.empty => Option.none,
        List.cons hd rest =>
            match hd {
                MatchCase.mc name _ _ =>
                    let wildcard_id : Identifier := Identifier.id "_" in
                    if Similar.similar name wildcard_id
                    then find_inductive_for_cases_by_constructor rest scope
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

/// Extract the last dotted segment of a name string (e.g. "List.cons" ->
/// "cons", "cons" -> "cons") -- `String.get`-driven scan mirrors
/// `lang/module.mo`'s own `string_find_last_slash_go` (same idiom,
/// different delimiter). Used by `type_check_free_var_con` below.
#[terminating]
def last_dotted_segment_go (s : String) (idx : I64) : String :=
    if I64.lt idx 0 then s
    else
        match (String.get s idx : Option U8) {
            Option.some byte_val =>
                if U8.beq byte_val 46u8 then // '.' is ASCII 46
                    String.slice s (idx + 1) (String.length s)
                else
                    last_dotted_segment_go s (idx - 1),
            Option.none => s
        }

def last_dotted_segment (s : String) : String :=
    last_dotted_segment_go s (String.length s - 1)

/// Fallback for `type_check_free_var`: `id` might be a qualified (or
/// bare) CONSTRUCTOR reference in value position (`List.cons`,
/// `Command.help`, `Option.none`, ...) rather than a def/class method.
/// Constructors are registered in scope under their bare name only
/// (`lang/scope.mo`'s `add_constructors_go`, the same convention
/// `match_case_name`'s pattern-stripping already relies on for match
/// arms), so a qualified value reference like `List.cons` never
/// resolves via `scope_resolve_name`'s plain `def_refs` lookup -- this
/// was `type_check_free_var`'s biggest single remaining gap (confirmed
/// via lang/codegen/emit.mo: ~100 of its "unknown variable" errors were
/// all qualified constructor references -- `List.cons`, `Option.none`,
/// `Def.mk`, `Inductive.mk`, ...).
///
/// Once found, this trusts `expected_type` AS-IS for the returned type
/// -- no Pi-chain-building here (an earlier version of this function
/// built one from the constructor's own arity, e.g. `Term.hole ->
/// Term.hole -> expected_type` for a 2-arg constructor; that was WRONG
/// and got caught by this round's own regression-check discipline: for
/// a constructor applied to N args, `type_check_var` is reached exactly
/// once, from the INNERMOST `type_check_app` frame, by which point
/// `expected_type` has ALREADY been Pi-wrapped N times by that same
/// recursive machinery (`type_check_app`'s own `f_expected := Term.pi
/// a_typ expected_type` at each level) -- it's already exactly the
/// right N-argument function-type shape. Wrapping more Pi's around an
/// already-correctly-shaped type produced a type one level too deep,
/// surfacing as `type mismatch: expected (List X), found (_ -> (_ ->
/// _))` on any 2+-arg constructor value used inside a context whose own
/// expected type starts as `Term.hole` (any match-arm body -- see
/// `type_check_case_body_checked` above, which always checks a case
/// body against `Term.hole`). Trusting `expected_type` directly matches
/// `type_check_con`'s own established pattern exactly (`ok (mk_typed
/// (Term.con c) expected_type)`) and `scope_resolve_name`'s success arm
/// just above (which returns the def's own STORED signature,
/// unconditionally, ignoring `expected_type` too) -- constructors just
/// have no stored signature to return (`add_constructors_go` registers
/// them with `sig := Term.hole`, unusable), so the caller-built
/// `expected_type` is the only real type information available here.
def type_check_free_var_con (id : Identifier) (expected_type : Term) (dbg : DebugName) (scope : Scope) : Result TypeError TypedTerm :=
    let bare_name : Identifier := match id { Identifier.id s => Identifier.id (last_dotted_segment s) } in
    let con_mp : ModulePath := ModulePath.mp (List.cons bare_name List.empty) in
    match scope_find_inductive_by_constructor con_mp scope {
        Option.some ind =>
            match find_constructor_in_inductive ind con_mp {
                Option.some _ => ok (mk_typed (Term.var sentinel dbg) expected_type),
                Option.none => err (TypeError.unknown_var (NameRef.nid id)),
            },
        Option.none => err (TypeError.unknown_var (NameRef.nid id)),
    }

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
                            type_check_free_var_con id expected_type dbg scope,
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

/// Is this Term a bare, uninformative `Term.hole`?
def is_hole (t : Term) : Bool :=
    match t {
        Term.hole => true,
        _ => false,
    }

/// Type check a lambda expression.
def type_check_lam (dbg : DebugName) (t : Term) (body : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match expected_type {
        Term.pi arg_typ ret_typ =>
            // Prefer the lambda's OWN written param type `t` over `arg_typ`
            // (the type `type_check_app` infers for the ARGUMENT this
            // lambda is about to be applied to) whenever `t` isn't itself
            // `Term.hole` -- an explicit annotation in the source is real
            // information; `arg_typ` can be `Term.hole` even when the
            // written annotation isn't, since ordinary top-level defs are
            // registered in scope with `sig := Term.hole` (`build_scope_
            // def`, lang/scope.mo) -- a cross-def reference's type comes
            // back as a placeholder regardless of what its callee actually
            // declared. This matters for every `let x : T := f y in body`
            // (desugars to exactly this `App(Lam{t=T}, f y)` shape,
            // `let_term_body`/do-block `let`, both lang/parser.mo) --
            // without preferring `t`, `x`'s local type silently degrades
            // to `Term.hole` even though `T` was written right there,
            // breaking downstream precision (e.g. match-case validation
            // needing `x`'s real type to disambiguate a constructor
            // collision -- confirmed via lang/main.mo's own `main`, see
            // plans/bootstrapping/self-hosted-compiler.md's changelog).
            let bound_typ : Term := if is_hole t then arg_typ else t in
            let extended_types : List Term := List.cons bound_typ local_types in
            let lv : LocalVar := {
                name := debug_name_to_id dbg,
                typ := bound_typ,
                multiplicity := Multiplicity.many,
            } in
            let extended_locals : LocalScope := scope_push_local lv locals in
            match type_check body ret_typ scope extended_types extended_locals {
                ok body_tt =>
                    let checked_body : Term := tt_term body_tt in
                    let lam_term : Term := Term.lam dbg bound_typ checked_body in
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
    let a_expected : Term := app_arg_expected_type f in
    match type_check a a_expected scope local_types locals {
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

/// When `f` is an inline lambda with a KNOWN (non-hole) declared param
/// type -- the shape every `let x : T := value in body` (and do-block
/// equivalent) desugars to (`Term.app (Term.lam dbg T body) value`) --
/// check the argument against that declared type instead of the
/// otherwise-uninformative `Term.hole`. Without this, a term whose own
/// checking depends entirely on an ambient expected type (a struct
/// literal with no `: StructName` self-annotation is the motivating
/// case -- field names alone don't determine a unique struct) has no
/// way to learn it, since the argument is checked BEFORE `f`, and
/// `type_check_lam`'s own `is_hole` preference (see its doc comment)
/// only recovers `T` on the FUNCTION/bound-variable side, never threads
/// it back to the argument being checked against it. Ordinary function
/// application -- `f` anything other than an inline lambda, by far the
/// common case (a named function reference, a partially-applied
/// multi-arg call, ...) -- is completely unaffected: falls through to
/// the previous `Term.hole` behavior unchanged. Mirrors the reference
/// compiler's own dedicated `App(Lam{param_typ}, arg)` special case
/// (`core_check.rs`).
def app_arg_expected_type (f : Term) : Term :=
    match f {
        Term.lam _dbg param_typ _body => param_typ,
        _ => Term.hole,
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

/// Type check a constructor application: verifies the referenced
/// inductive/constructor actually exist, that `c.num_args` matches the
/// constructor's own declared arity, and that each PRESENT argument
/// (`c.args` is sparse — `Option.none` marks an unfilled, not-yet-
/// applied position, matching `lower_core_ir.mo`'s own doc comment on
/// `Con`'s shape) type-checks against that positional param's declared
/// type. Mirrors `core/src/core_check.rs`'s own `CoreTerm::Con` arm —
/// including its "unregistered inductive" fallback (still individually
/// check each present arg, just without field-type correlation, rather
/// than rejecting outright) — scaled down to this checker's existing
/// capabilities: no metavariable-based type-parameter recovery (unlike
/// the Rust reference's `fresh_meta`/`unify` substitution), so a
/// parametric constructor's arg types are checked against their
/// LITERAL declared param types, not an instantiated one — the same
/// simplification `type_check_app`/`extract_pi_ret` already make
/// (comparing against a Pi's own declared arg type directly, no
/// substitution either).
///
/// Note: unlike `type_check_con`, `type_check_ntv` just below needs no
/// equivalent treatment — it was never actually a stub needing this
/// kind of check. Neither `Term.con` nor `Term.ntv` is ever produced by
/// this codebase's own parser (`lang/parser.mo`) today; both exist for
/// the lowering/pretty-printing pipeline (`lang/lower_core_ir.mo`,
/// `lang/pretty.mo`) and hand-built test fixtures. This still closes
/// real technical debt (`type_check_con` was silently accepting any
/// arity/shape) and is exercised by this file's own `#[test]`s below,
/// even though no corpus `.mo` file's `check` run currently reaches it.
def type_check_con (c : Con) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match c {
        mk cname typ_name num_args args =>
            match typ_name {
                ModulePath.mp ids =>
                    let full_name : ModulePath := ModulePath.mp (list_append ids (List.cons cname List.empty)) in
                    match scope_find_inductive typ_name scope {
                        err _ =>
                            match check_con_args_untyped args scope local_types locals {
                                ok _ => ok (mk_typed (Term.con c) expected_type),
                                err e => err e,
                            },
                        ok ind =>
                            match find_constructor_in_inductive ind full_name {
                                Option.none => err (TypeError.unknown_constructor (NameRef.nmp full_name)),
                                Option.some ctor =>
                                    match ctor {
                                        InductConstructor.mk _ params _ =>
                                            if I64.beq num_args (List.length params) then
                                                match check_con_args_against_params args params scope local_types locals {
                                                    ok _ => ok (mk_typed (Term.con c) expected_type),
                                                    err e => err e,
                                                }
                                            else
                                                err (TypeError.custom (con_arity_msg full_name num_args (List.length params)))
                                    }
                            }
                    }
            }
    }

def con_arity_msg (full_name : ModulePath) (got : I64) (want : I64) : String :=
    "constructor arity mismatch: " ++ show_module_path full_name ++ " expects "
        ++ I64.to_string want ++ " arg(s), got " ++ I64.to_string got

/// Type check a struct-literal expression (`{ field := value, ... }`).
/// Resolves which struct it builds (from its own self-annotation if
/// present, otherwise from `expected_type`), reorders the literal's
/// (unordered, name-matched) fields into the struct's own DECLARED
/// field order, and reuses `check_con_args_against_params` -- the same
/// per-argument type-checking `type_check_con` uses -- against the
/// synthetic single-constructor `Inductive` `build_scope_struct`
/// registers for every struct (name `mk`, mirroring the reference's own
/// desugaring of a struct literal into a constructor application,
/// `core/src/core_check.rs`'s `desugar_struct_literals`). Mirrors the
/// reference's own leniency (`check_struct_fields`, core_check.rs):
/// fields present in the literal are checked against their declared
/// type; fields ABSENT from the literal (whether or not the struct
/// declares a default for them) are not separately validated here --
/// same as `check_con_args_against_params`'s existing `Option.none`
/// handling for any other constructor call with sparse args.
def type_check_struct_lit (fields : List StructLitField) (type_name : Option Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match struct_lit_head_name type_name expected_type {
        Option.none =>
            err (TypeError.custom "cannot infer struct type for struct literal (no `: StructName` annotation and no expected type from context)"),
        Option.some sname =>
            let typ_mp : ModulePath := ModulePath.mp (List.cons sname List.empty) in
            match scope_find_inductive typ_mp scope {
                err _ => err (TypeError.unknown_type (NameRef.nmp typ_mp)),
                ok ind =>
                    match ind {
                        Inductive.mk _ _ _ ctors _ _ =>
                            match ctors {
                                List.empty => err (TypeError.custom (String.concat "struct has no registered constructor: " (show_module_path typ_mp))),
                                List.cons ctor _ =>
                                    match ctor {
                                        InductConstructor.mk con_name params _ =>
                                            let args : List (Option Term) := struct_lit_build_args params fields in
                                            match check_con_args_against_params args params scope local_types locals {
                                                err e => err e,
                                                ok _ =>
                                                    let mk_name : Identifier := struct_lit_con_name con_name in
                                                    let c : Con := Con.mk mk_name typ_mp (List.length params) args in
                                                    let result_typ : Term := match type_name {
                                                        Option.some _ => Term.var sentinel (DebugName.named sname),
                                                        Option.none => expected_type,
                                                    } in
                                                    ok (mk_typed (Term.con c) result_typ),
                                            }
                                    }
                            }
                    }
            }
    }

/// The struct's own type name, wherever it comes from: the literal's
/// own `: StructName` self-annotation if present, otherwise whatever
/// concrete head type `expected_type` names -- same "prefer explicit,
/// fall back to inference context" shape `type_check_lam`'s `is_hole`
/// preference uses.
def struct_lit_head_name (type_name : Option Term) (expected_type : Term) : Option Identifier :=
    match type_name {
        Option.some tn => type_head_name tn,
        Option.none => type_head_name expected_type,
    }

/// `InductConstructor.mk`'s own `name` field is a full `ModulePath`
/// (`build_scope_struct` registers it as `ModulePath.mp [mk]`) --
/// `Con.mk` wants just the bare constructor `Identifier`, same as
/// every other constructor-application site in this file.
def struct_lit_con_name (con_mp : ModulePath) : Identifier :=
    match con_mp {
        ModulePath.mp ids =>
            match list_last ids {
                Option.some id => id,
                Option.none => Identifier.id "mk",
            }
    }

#[terminating]
def list_last (ids : List Identifier) : Option Identifier :=
    match ids {
        List.empty => Option.none,
        List.cons hd rest =>
            match rest {
                List.empty => Option.some hd,
                List.cons _ _ => list_last rest,
            }
    }

/// Reorders a struct literal's (name-matched, any-order) fields into
/// the struct's own declared `Param` order, producing the sparse
/// `List (Option Term)` shape `check_con_args_against_params`/`Con`
/// expect. A literal field with no matching declared param is simply
/// ignored (same leniency the reference's `check_struct_fields` has --
/// it only ever walks the struct's OWN declared fields, never the
/// literal's).
#[terminating]
def struct_lit_build_args (params : List Param) (fields : List StructLitField) : List (Option Term) :=
    match params {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Param.mk pname _ _ _ _ =>
                    List.cons (struct_lit_find_field fields pname) (struct_lit_build_args rest fields)
            }
    }

#[terminating]
def struct_lit_find_field (fields : List StructLitField) (name : Identifier) : Option Term :=
    match fields {
        List.empty => Option.none,
        List.cons f rest =>
            match f {
                StructLitField.mk fname fvalue =>
                    if id_eq fname name then Option.some fvalue else struct_lit_find_field rest name
            }
    }

/// Type check a struct-update expression (`{ base with field := value,
/// ... }`). Mirrors the reference's own acknowledged simplification for
/// this construct (`infer_lit`'s `CoreLit::StructUpdate` arm,
/// core/src/core_check.rs): `base`'s type IS knowable (it's an ordinary
/// term), so the overall result type is `base`'s own type unchanged;
/// each replacement field VALUE is still individually checked (to catch
/// an outright ill-typed update), but not correlated with that
/// specific field's own declared type -- the reference doesn't either
/// (same missing-registry limitation plain `StructLit` without a
/// self-annotation has).
def type_check_struct_update (base : Term) (fields : List StructLitField) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match type_check base Term.hole scope local_types locals {
        err e => err e,
        ok base_tt =>
            match struct_update_check_fields fields scope local_types locals {
                err e => err e,
                ok _ =>
                    let base_term : Term := tt_term base_tt in
                    let base_typ : Term := tt_typ base_tt in
                    let updated : Term := Term.lit (Literal.struct_update base_term fields) in
                    ok (mk_typed updated base_typ),
            }
    }

#[terminating]
def struct_update_check_fields (fields : List StructLitField) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError Bool :=
    match fields {
        List.empty => ok true,
        List.cons f rest =>
            match f {
                StructLitField.mk _ value =>
                    match type_check value Term.hole scope local_types locals {
                        ok _ => struct_update_check_fields rest scope local_types locals,
                        err e => err e,
                    }
            }
    }

/// Individually type-check each present argument with no expected type
/// (`Term.hole` — same "no information available" meaning `type_check`
/// itself already gives `Term.hole` elsewhere) — the fallback for a
/// constructor whose inductive type isn't registered in scope, matching
/// `core_check.rs`'s own documented simplification for this case.
#[terminating]
def check_con_args_untyped (args : List (Option Term)) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError Bool :=
    match args {
        List.empty => ok true,
        List.cons a rest =>
            match a {
                Option.none => check_con_args_untyped rest scope local_types locals,
                Option.some term =>
                    match type_check term Term.hole scope local_types locals {
                        ok _ => check_con_args_untyped rest scope local_types locals,
                        err e => err e,
                    }
            }
    }

/// Zip each present argument against the constructor's own declared
/// params, positionally, checking each present arg against its param's
/// literal declared type. If `args` somehow outlasts `params` (shouldn't
/// happen once `type_check_con`'s own arity check has already run, but
/// stay defensive rather than silently skipping the overflow), the
/// remaining args fall back to `check_con_args_untyped`.
#[terminating]
def check_con_args_against_params (args : List (Option Term)) (params : List Param) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError Bool :=
    match args {
        List.empty => ok true,
        List.cons a rest =>
            match params {
                List.empty => check_con_args_untyped args scope local_types locals,
                List.cons p prest =>
                    match a {
                        Option.none => check_con_args_against_params rest prest scope local_types locals,
                        Option.some term =>
                            match p {
                                Param.mk _ ptyp _ _ _ =>
                                    match type_check term ptyp scope local_types locals {
                                        ok _ => check_con_args_against_params rest prest scope local_types locals,
                                        err e => err e,
                                    }
                            }
                    }
            }
    }

/// Type check a native term. NOT a stub needing "real" checking despite
/// looking like one — natives are opaque to the type checker BY DESIGN,
/// mirroring `core/src/core_check.rs`'s own `CoreTerm::Ntv` arm exactly
/// (its own doc comment: "there is no native-signature registry to
/// consult, even in the real checker"). Accepting `expected_type`
/// unconditionally is that same "no information, defer to the use
/// site" behavior — Rust's `infer`/`check` split expresses it as
/// `Ok(CoreTerm::Hole)` from `infer`, which then trivially unifies
/// against whatever `check` compares it to; this checker's single
/// bidirectional `expected_type` parameter already plays both roles.
def type_check_ntv (n : Native) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    ok (mk_typed (Term.ntv n) expected_type)

// --- Tests for type_check_con ---
//
// Neither `Term.con` nor `Term.ntv` is ever produced by this codebase's
// own parser, so no corpus `.mo` file's `check` run exercises
// `type_check_con` — these tests are its only real coverage. Builds a
// minimal single-constructor `Box` inductive (one param, declared type
// `Term.type_ 2`) directly into a fresh `Scope`, mirroring
// `lang/tests/scope_tests.mo`/`types_tests.mo`'s own hand-built-fixture
// convention. The param's argument uses `Term.type_ N` specifically
// (not a literal/free-var) because `type_check_sort_full` is one of the
// few leaf checkers that actually compares against `expected_type`
// (see `type_check_ntv`'s own doc comment above: most leaf cases here
// just infer and return, ignoring `expected_type` — a literal argument
// would trivially "pass" any declared param type, proving nothing).

def box_ctor_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Box") List.empty)

def box_ctor_full_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Box") (List.cons (Identifier.id "box") List.empty))

def box_param : Param := Param.mk (Identifier.id "x") (Term.type_ 2) Multiplicity.many Option.none List.empty

def box_constructor : InductConstructor := InductConstructor.mk box_ctor_full_path (List.cons box_param List.empty) (Term.type_ 3)

def box_inductive : Inductive := Inductive.mk box_ctor_path List.empty (Term.type_ 3) (List.cons box_constructor List.empty) List.empty Visibility.package_private

def box_scope : Scope := {
    module_id := box_ctor_path,
    scope := scope_data_add_inductive scope_data_empty box_inductive,
    parent := Option.none,
}

#[test]
def test_type_check_con_valid_arg_ok : Bool :=
    let arg : Term := Term.type_ 1 in
    let c : Con := Con.mk (Identifier.id "box") box_ctor_path 1 (List.cons (Option.some arg) List.empty) in
    match type_check_con c Term.hole box_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_type_check_con_wrong_arg_type_rejected : Bool :=
    // `x`'s declared param type is `Term.type_ 2` — a sort at level 5
    // is NOT a valid inhabitant (`type_check_sort_full`'s own
    // `expected_level < level` branch), so this must be rejected.
    let bad_arg : Term := Term.type_ 5 in
    let c : Con := Con.mk (Identifier.id "box") box_ctor_path 1 (List.cons (Option.some bad_arg) List.empty) in
    match type_check_con c Term.hole box_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

#[test]
def test_type_check_con_wrong_arity_rejected : Bool :=
    // `box` declares exactly 1 param — claiming 2 must be rejected
    // regardless of `args`' own content.
    let arg : Term := Term.type_ 1 in
    let c : Con := Con.mk (Identifier.id "box") box_ctor_path 2 (List.cons (Option.some arg) (List.cons (Option.some arg) List.empty)) in
    match type_check_con c Term.hole box_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

#[test]
def test_type_check_con_unknown_constructor_rejected : Bool :=
    let arg : Term := Term.type_ 1 in
    let c : Con := Con.mk (Identifier.id "no_such_ctor") box_ctor_path 1 (List.cons (Option.some arg) List.empty) in
    match type_check_con c Term.hole box_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

#[test]
def test_type_check_con_missing_arg_skipped : Bool :=
    // A `None` slot (an unfilled, not-yet-applied position — see
    // `Con`'s own doc comment on `type_check_con`) must not be
    // typechecked, only skipped.
    let c : Con := Con.mk (Identifier.id "box") box_ctor_path 1 (List.cons Option.none List.empty) in
    match type_check_con c Term.hole box_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_type_check_con_unregistered_inductive_falls_back : Bool :=
    // `typ_name` refers to an inductive that isn't in scope at all —
    // still individually checks present args (a bad one is still
    // caught), just without field-type correlation.
    let unknown_typ : ModulePath := ModulePath.mp (List.cons (Identifier.id "NoSuchType") List.empty) in
    let good_arg : Term := Term.type_ 1 in
    let c_ok : Con := Con.mk (Identifier.id "whatever") unknown_typ 1 (List.cons (Option.some good_arg) List.empty) in
    match type_check_con c_ok Term.hole box_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

// --- Tests for type_check_struct_lit ---
//
// A hand-built `Point { x, y }` scope, same fixture convention as
// `box_scope` above -- mirrors exactly what `build_scope_struct`
// (lang/scope.mo) itself registers for a real `struct Point { x : T,
// y : T }` declaration (type path `[Point]`, single synthetic
// constructor path `[mk]`).

def point_type_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Point") List.empty)

def point_mk_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "mk") List.empty)

def point_x_param : Param := Param.mk (Identifier.id "x") (Term.type_ 2) Multiplicity.many Option.none List.empty

def point_y_param : Param := Param.mk (Identifier.id "y") (Term.type_ 2) Multiplicity.many Option.none List.empty

def point_params : List Param := List.cons point_x_param (List.cons point_y_param List.empty)

def point_constructor : InductConstructor := InductConstructor.mk point_mk_path point_params Term.hole

def point_inductive : Inductive := Inductive.mk point_type_path List.empty Term.hole (List.cons point_constructor List.empty) List.empty Visibility.package_private

def point_scope : Scope := {
    module_id := point_type_path,
    scope := scope_data_add_inductive scope_data_empty point_inductive,
    parent := Option.none,
}

def point_type_ref : Term := Term.var sentinel (DebugName.named (Identifier.id "Point"))

#[test]
def test_type_check_struct_lit_self_annotated_ok : Bool :=
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.type_ 1) in
    let f2 : StructLitField := StructLitField.mk (Identifier.id "y") (Term.type_ 1) in
    let fields : List StructLitField := List.cons f1 (List.cons f2 List.empty) in
    let type_name : Option Term := Option.some point_type_ref in
    match type_check_struct_lit fields type_name Term.hole point_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_type_check_struct_lit_from_expected_type_ok : Bool :=
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.type_ 1) in
    let f2 : StructLitField := StructLitField.mk (Identifier.id "y") (Term.type_ 1) in
    let fields : List StructLitField := List.cons f1 (List.cons f2 List.empty) in
    let no_annotation : Option Term := Option.none in
    match type_check_struct_lit fields no_annotation point_type_ref point_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_type_check_struct_lit_no_annotation_no_expected_rejected : Bool :=
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.type_ 1) in
    let fields : List StructLitField := List.cons f1 List.empty in
    let no_annotation : Option Term := Option.none in
    match type_check_struct_lit fields no_annotation Term.hole point_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

#[test]
def test_type_check_struct_lit_wrong_field_type_rejected : Bool :=
    // `x`'s declared param type is `Term.type_ 2` -- a sort at level 5
    // is not a valid inhabitant, same reasoning as
    // `test_type_check_con_wrong_arg_type_rejected` above.
    let bad_f : StructLitField := StructLitField.mk (Identifier.id "x") (Term.type_ 5) in
    let fields : List StructLitField := List.cons bad_f List.empty in
    let type_name : Option Term := Option.some point_type_ref in
    match type_check_struct_lit fields type_name Term.hole point_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

#[test]
def test_type_check_struct_lit_missing_field_ok : Bool :=
    // Only `x` provided, `y` entirely absent -- must still succeed,
    // mirroring the reference compiler's own leniency here
    // (`check_struct_fields`, core_check.rs: only fields PRESENT in the
    // literal are checked, absence isn't itself an error at this
    // layer).
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.type_ 1) in
    let fields : List StructLitField := List.cons f1 List.empty in
    let type_name : Option Term := Option.some point_type_ref in
    match type_check_struct_lit fields type_name Term.hole point_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_type_check_struct_lit_unknown_struct_rejected : Bool :=
    let unknown_ref : Term := Term.var sentinel (DebugName.named (Identifier.id "NoSuchStruct")) in
    let fields : List StructLitField := List.empty in
    let type_name : Option Term := Option.some unknown_ref in
    match type_check_struct_lit fields type_name Term.hole point_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

#[test]
def test_type_check_struct_lit_extra_unknown_field_ignored : Bool :=
    // A literal field with no matching declared param is silently
    // ignored, same leniency as the reference's own `check_struct_fields`
    // (which only ever walks the struct's OWN declared fields).
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.type_ 1) in
    let f2 : StructLitField := StructLitField.mk (Identifier.id "y") (Term.type_ 1) in
    let extra : StructLitField := StructLitField.mk (Identifier.id "z_not_a_field") (Term.type_ 1) in
    let fields : List StructLitField := List.cons f1 (List.cons f2 (List.cons extra List.empty)) in
    let type_name : Option Term := Option.some point_type_ref in
    match type_check_struct_lit fields type_name Term.hole point_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

// --- Tests for type_check_struct_update ---

/// A bound local variable `p : Point` (de Bruijn index 0), for
/// `{ p with ... }`-shaped tests.
def point_local_types : List Term := List.cons point_type_ref empty_local_types

def point_var : Term := Term.var 0 (DebugName.named (Identifier.id "p"))

#[test]
def test_type_check_struct_update_ok : Bool :=
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.type_ 1) in
    let fields : List StructLitField := List.cons f1 List.empty in
    match type_check_struct_update point_var fields Term.hole point_scope point_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_type_check_struct_update_result_type_is_base_type : Bool :=
    let fields : List StructLitField := List.empty in
    match type_check_struct_update point_var fields Term.hole point_scope point_local_types empty_locals {
        ok tt => match type_head_name (tt_typ tt) {
            Option.some id => id_eq id (Identifier.id "Point"),
            Option.none => false,
        },
        err _ => false,
    }

#[test]
def test_type_check_struct_update_bad_base_rejected : Bool :=
    // `base` is an out-of-range de Bruijn index -- `type_check base
    // Term.hole ...` must reject it, same as any other ill-formed term.
    let bad_base : Term := Term.var 99 (DebugName.named (Identifier.id "nope")) in
    let fields : List StructLitField := List.empty in
    match type_check_struct_update bad_base fields Term.hole point_scope point_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }
