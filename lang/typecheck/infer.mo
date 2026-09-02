use lang.types {
  Con, DebugName, Identifier, Inductive, InductConstructor,
  Literal, LocalScope, LocalVar, MatchCase, ModulePath, NameRef, NumSuffix,
  Native, Param, Scope, ScopeClassDef, ScopeDef, ScopeError, Similar,
  StructLitField, Term, TypeConstraint, TypeError,
  app, con, custom, forall, hole, id, id_eq, if_, lam, list_rev_loop,
  list_reverse, lit, many, match_, mc, mk, mp, name, named, nid, not_a_type,
  ntv, num, pi, show_identifier, show_module_path, str, type_,
  unknown_constructor, unknown_type, unknown_var, unnamed, var,
}
use lang.scope {
  DictBinding, build_dict_field_projection_checked, build_scope_def,
  dict_binding_class_of, dict_param_name, find_constructor_in_inductive,
  find_matching_instance, flatten_call_spine, inductive_has_constructor, list_append,
  mangle_instance_method_name, mangled_to_identifier, rebuild_call,
  resolve_dict_args, scope_data_add_inductive, scope_data_classes,
  scope_data_empty, scope_find_all_inductives_by_constructor, scope_find_class,
  scope_find_class_def_by_name, scope_find_def_params, scope_find_def_return_type,
  scope_find_inductive, scope_find_inductive_by_constructor,
  scope_find_local, scope_globals, scope_instance_candidates, scope_push_local,
  scope_resolve_name,
}
use lang.typecheck.name_subst {name_subst_term}
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
///
/// `Term.quote_`/`Term.var_macro` are macro-expansion-only shapes --
/// `quote_` is resolved away by `macro_expand.mo`'s `resolve_quote`
/// before type-checking ever runs, and `var_macro` only ever appears
/// inside an unexpanded macro template. Neither should reach here in
/// the real pipeline (`expand_decls` always runs first), but this match
/// previously had no arm for either -- a genuine non-exhaustive-match
/// crash risk (no `#[partial]` on this def) if a macro ever expanded to
/// another macro call without fully resolving it. A clean `TypeError`
/// is safer than a raw interpreter crash either way.
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
        Term.quote_ _ => err (TypeError.custom "unresolved quote reached the type checker (macro expansion should have resolved it first)"),
        Term.var_macro _ _ => err (TypeError.custom "unresolved macro-template variable reached the type checker (macro expansion should have resolved it first)"),
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
//
// `derive_instance_key` (a `class_def`/`expected_type` -> `InstanceKey`
// stub that always returned an empty-`args` key, matching nothing real —
// every corpus instance declares at least one concrete/wildcard arg) and
// the old `resolve_class_method` (whose own class lookup via
// `scope_find_inductive` could never succeed either -- classes are
// registered into `ScopeData.classes`, a field that reader never looked
// at) have both been retired in favor of the resolution below, which
// reuses `lang.scope`'s already corpus-proven, wildcard-aware
// `find_matching_instance` instead of a second, from-scratch stub. See
// `bootstrapping/unify-check-compile-test-elaboration.md`.

/// Derive a class-method call's carrier type from the ALREADY-ELABORATED
/// `expected_type` a class-method leaf sees. `type_check_app` (below)
/// checks each argument before the function it's applied to, so by the
/// time a bare class-method var is resolved, `expected_type` is already
/// a real Pi-chain built from the call's actual (already bidirectionally
/// checked) argument types -- not a syntactic guess. Prefers the first
/// non-hole Pi domain (the carrier position for every single-param class
/// in this corpus); falls back to the type itself for a nullary method
/// checked directly against its own call site's expected return type
/// (e.g. `Default.default`). Deliberately scoped to single-carrier
/// resolution -- heterogeneous/multi-param classes (`Map`, `From`,
/// `IndexedMonad`) fall through to the abstract-signature fallback below,
/// same as they do today.
def carrier_from_expected_type (t : Term) : Option Term :=
    match t {
        Term.pi arg_typ ret_typ =>
            if is_uninformative_carrier arg_typ then carrier_from_expected_type ret_typ else Option.some arg_typ,
        Term.hole => Option.none,
        _ => Option.some t,
    }

/// `is_hole` alone isn't enough: a bare literal checked in pure-infer
/// mode (`type_check_lit`'s `Literal.str`/`Literal.num`/... arms) reports
/// its OWN type as `Term.type_ 1` (a universe placeholder, not the
/// literal's real type -- `String`/`I64`/...), confirmed via a direct
/// repro: `"/" ++ rest`'s OUTER `++` carrier came back as literally
/// `Type` instead of `String`, because `"/"`'s sibling operand `rest`'s
/// own Pi-domain position was checked first and happened to be a nested
/// `++` chain whose OWN innermost literal polluted an intermediate Pi
/// arg with `Term.type_ 1`. Treating it the same as `Term.hole` here --
/// skip to the next Pi domain rather than accepting it as a carrier --
/// mirrors why the OLD syntactic pass (`lang.scope`'s `infer_carrier_
/// type`) never trusted a type-checker-reported literal type either,
/// matching on the literal VALUE directly instead (`literal_carrier_
/// type`).
def is_uninformative_carrier (t : Term) : Bool :=
    match t {
        Term.hole => true,
        Term.type_ _ => true,
        _ => false,
    }

/// Is there already a bound local dict param for `cls_name` in scope
/// (Phase 3's own `__dict_ClassName` naming, `lang.scope`'s
/// `dict_param_name`)? D5 forwarding -- inside a still-generic
/// constrained def's own body, the concrete instance isn't known yet,
/// only a dict VALUE already bound as a parameter.
def local_dict_for_class (cls_name : ModulePath) (locals : LocalScope) : Option Identifier :=
    match scope_find_local (Identifier.id (dict_param_name cls_name)) locals {
        Option.some lv => Option.some lv.name,
        Option.none => Option.none,
    }

#[partial]
def local_vars_flat (locals : LocalScope) : List LocalVar :=
    match locals {
        mk vars parent =>
            match parent {
                Option.some p => list_append vars (local_vars_flat p),
                Option.none => vars,
            },
    }

#[partial]
def dict_bindings_of_vars (vars : List LocalVar) : List DictBinding :=
    match vars {
        List.empty => List.empty,
        List.cons lv rest =>
            match dict_binding_class_of lv.name {
                Option.some cls => List.cons (DictBinding.mk cls lv.name) (dict_bindings_of_vars rest),
                Option.none => dict_bindings_of_vars rest,
            },
    }

/// Every currently-bound local matching Phase 3's dict-param naming, as
/// the `DictBinding` list `resolve_dict_args` (reused as-is below)
/// expects for its own D5-forwarding check on a NESTED constraint (the
/// `HAdd`-forwards-to-`Add` shape: the matched D4 instance is itself
/// constrained, and that inner constraint might ALSO already be
/// satisfied by a dict this call is nested inside).
def dict_env_from_locals (locals : LocalScope) : List DictBinding :=
    dict_bindings_of_vars (local_vars_flat locals)

/// D4: fresh concrete lookup, once no local dict forwards this class.
/// Mangles the concrete method's own name EXACTLY as `promote_instance_
/// defs` itself names it (so this resolves to a real, already-registered
/// def -- `elaborate_loaded_modules`, `lang/module.mo`, always runs
/// promotion before building the `Scope` this checks against), confirms
/// it's actually in scope (a clean diagnostic instead of a dangling
/// reference, if promotion silently skipped this instance for a missing
/// method), and -- only when the MATCHED INSTANCE ITSELF still carries
/// constraints (`HAdd`-forwards-to-`Add`) -- resolves and pre-applies its
/// own dict argument(s) via the existing, reused `resolve_dict_args`.
/// Strip `n` leading `Term.pi` binders (skipping over any `Term.forall`
/// binders first at each step -- they don't correspond to an applied
/// value argument), returning the final codomain. Needed because
/// `resolve_class_method_d4`'s reported type must be the RESOLVED
/// concrete def's own real signature (peeled by however many dict args
/// got pre-applied), not `expected_type` verbatim -- `expected_type`
/// itself can be partially uninformative (a literal operand elsewhere
/// in the SAME `++` chain reports `Term.type_ 1` in pure-infer mode, not
/// its real type -- see `is_uninformative_carrier`'s own doc comment),
/// and reusing it verbatim as this call's reported type would cascade
/// that uninformativeness upward into the NEXT enclosing `type_check_
/// app`'s own carrier derivation -- confirmed as the actual root cause
/// of a real repro (the self-hosted test driver's own synthesized
/// summary line) via direct debugging.
#[partial]
def strip_n_pis (typ : Term) (n : I64) : Term :=
    if I64.lt n 1 then typ
    else
        match typ {
            Term.forall _ _ body => strip_n_pis body n,
            Term.pi _ ret => strip_n_pis ret (n - 1),
            _ => typ,
        }

def resolve_class_method_d4
    (ins_cls_name : ModulePath) (method_name : Identifier)
    (ins_constraints : List TypeConstraint) (ins_args : List Term) (carrier : Term)
    (expected_type : Term) (scope : Scope) (locals : LocalScope)
    : Result TypeError TypedTerm :=
    let mangled := mangle_instance_method_name ins_cls_name ins_args method_name in
    let mangled_id := mangled_to_identifier mangled in
    match scope_resolve_name (NameRef.nid mangled_id) scope locals {
        err _ => err (TypeError.custom "instance is missing its promoted method"),
        ok resolved_sd =>
            let real_sig : Term := match resolved_sd { mk _ _ sig_ _ => sig_ } in
            let mangled_ref : Term := Term.var sentinel (DebugName.named mangled_id) in
            match ins_constraints {
                List.empty => ok (mk_typed mangled_ref real_sig),
                List.cons _ _ =>
                    let classes := scope_data_classes (scope_globals scope) in
                    let instances := scope_instance_candidates (scope_globals scope) ins_cls_name in
                    let dict_env := dict_env_from_locals locals in
                    // `List.empty` -- extending this call site with the same
                    // args-derived `extra_carriers` fallback `lang.scope`'s
                    // codegen pass now has (`resolve_dict_arg`'s own doc
                    // comment) is out of scope here: this checker-level path
                    // doesn't hard-fail on a miss anyway (see
                    // `resolve_class_method`'s own `err _ =>` fallback to the
                    // method's abstract signature, `type_check_free_var`),
                    // and every codegen path re-resolves this same call
                    // later via the now-fixed `lang.scope` pass regardless.
                    match resolve_dict_args classes instances dict_env carrier List.empty ins_constraints {
                        Option.none => err (TypeError.custom "cannot resolve inner instance dictionary"),
                        Option.some dict_args =>
                            let applied_typ : Term := strip_n_pis real_sig (List.length dict_args) in
                            ok (mk_typed (rebuild_call mangled_ref dict_args) applied_typ),
                    },
            },
    }

/// Resolve a class-method reference (`Show.show`, `Append.append`, ...)
/// to a concrete, elaborated `Term` -- D5 (an already-bound dict local
/// for this class) checked first, D4 (fresh concrete-instance lookup
/// from the carrier) as fallback, mirroring `lang.scope`'s own proven
/// Phase 4 dispatch ordering exactly. REQUIRES `promote_instance_defs`
/// (Phase 2) and `add_constraint_dict_params_decls` (Phase 3) to already
/// have run over the whole loaded module graph before this is called
/// (`elaborate_loaded_modules`, `lang/module.mo`) -- the mangled concrete
/// defs and dict-binding lambda params this depends on must already
/// exist in scope.
def resolve_class_method ({ class_name, name := method_name, .. } : ScopeClassDef) (expected_type : Term) (scope : Scope) (locals : LocalScope) : Result TypeError TypedTerm :=
    match scope_find_class class_name scope {
        Option.none => err (TypeError.custom "class not found in scope"),
        Option.some cls =>
            match local_dict_for_class class_name locals {
                Option.some dict_id =>
                    // `_checked` sibling, not `build_dict_field_projection`
                    // itself -- this result gets re-typechecked (this
                    // resolution happens while `elaborate_loaded_modules`'
                    // rewritten decls are later re-checked by `check_
                    // module_with_scope`), so it needs the checker's
                    // by-name free-var convention, not codegen's raw
                    // de-Bruijn-index-0 one. See both functions' own doc
                    // comments (`lang/scope.mo`) for the full D5 story.
                    let term := build_dict_field_projection_checked cls dict_id method_name List.empty in
                    ok (mk_typed term expected_type),
                Option.none =>
                    match carrier_from_expected_type expected_type {
                        Option.none => err (TypeError.custom "cannot infer carrier type for class method"),
                        Option.some carrier =>
                            let candidates := scope_instance_candidates (scope_globals scope) class_name in
                            match find_matching_instance candidates class_name carrier {
                                Option.none => err (TypeError.custom "no matching instance found"),
                                Option.some ins =>
                                    resolve_class_method_d4 ins.cls method_name ins.constraints ins.args carrier expected_type scope locals,
                            },
                    },
            },
    }

/// Type check a literal value.
/// A `NumSuffix`'s own real named type (`Term.var sentinel (DebugName.
/// named "I64")`, the same shape any other free type reference resolves
/// to) -- `lang/parser/number.mo`'s parser always attaches a suffix,
/// defaulting a bare unsuffixed literal (`0`) to `NumSuffix.i64` (see
/// its own `fail _ => success orig NumSuffix.i64`), so this covers every
/// `Literal.num`/`Literal.flt` unconditionally.
def num_suffix_type_name (suffix : NumSuffix) : String :=
    match suffix {
        NumSuffix.i8 => "I8", NumSuffix.i16 => "I16", NumSuffix.i32 => "I32", NumSuffix.i64 => "I64",
        NumSuffix.u8 => "U8", NumSuffix.u16 => "U16", NumSuffix.u32 => "U32", NumSuffix.u64 => "U64",
        NumSuffix.f32 => "F32", NumSuffix.f64 => "F64",
    }

def named_type_ref (s : String) : Term :=
    Term.var sentinel (DebugName.named (Identifier.id s))

def type_check_lit (value : Literal) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match value {
        // `Term.type_ 1` (a KIND, not a real type) used to be returned
        // here unconditionally regardless of what kind of literal this
        // actually is -- harmless as long as the caller's `expected_
        // type` was always `Term.hole` (`unify` accepts anything against
        // a hole), which was true for every match-arm body reached from
        // an ordinary top-level def until `check_def_with_scope` started
        // passing the def's own real declared type through. Once a real
        // expected type reaches here (e.g. an `I64`-returning def whose
        // body is a match with an `n => 0` arm), `unify (Term.type_ 1)
        // I64` correctly failed with "type mismatch: expected Type,
        // found I64" -- confirmed via a minimal repro (`def f (n : Nat)
        // : I64 := match n { zero => 0, succ m => 1 }`). Returning the
        // literal's own REAL type (from its `NumSuffix`, or `String` for
        // a string literal) fixes this at the source rather than
        // special-casing `unify` to treat `Term.type_ 1` as a wildcard
        // (which would also weaken genuine Sort/Type-as-value checks
        // elsewhere, e.g. the Sort/Pred tests).
        Literal.str s =>
            ok (mk_typed (Term.lit value) (named_type_ref "String")),
        Literal.num n suffix =>
            ok (mk_typed (Term.lit value) (named_type_ref (num_suffix_type_name suffix))),
        Literal.flt text suffix =>
            ok (mk_typed (Term.lit value) (named_type_ref (num_suffix_type_name suffix))),
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
            match validate_match_constructors cases sc_term sc_typ scope {
                err e => err e,
                ok maybe_ind => type_check_cases cases sc_term sc_typ maybe_ind expected_type scope local_types locals,
            },
        err e => err e,
    }

/// Validate that all non-wildcard case constructors belong to the same
/// inductive. Returns the resolved `Inductive` on success (threaded
/// through to `type_check_match_case` below so a case's own bound
/// pattern variables can be typed from the constructor's OWN declared
/// field types instead of `Term.hole` -- see `arg_types_for_case`'s own
/// doc comment for why this matters), or `Option.none` if no inductive
/// was determinable at all (skip validation, matches this function's
/// previous behavior exactly).
def validate_match_constructors (cases : List MatchCase) (scrutinee_term : Term) (scrutinee_typ : Term) (scope : Scope) : Result TypeError (Option Inductive) :=
    match find_inductive_for_cases cases scrutinee_term scrutinee_typ scope {
        err e => err e,
        ok maybe_ind =>
            match maybe_ind {
                Option.none => ok Option.none,
                Option.some ind =>
                    match validate_cases_against_inductive cases ind {
                        ok _ => ok (Option.some ind),
                        err e => err e,
                    },
            },
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
def find_inductive_for_cases (cases : List MatchCase) (scrutinee_term : Term) (scrutinee_typ : Term) (scope : Scope) : Result TypeError (Option Inductive) :=
    match con_owner_name scrutinee_term {
        Option.some typ_name =>
            match scope_find_inductive typ_name scope {
                ok ind =>
                    // `con_owner_name` fires for ANY qualified application
                    // head (e.g. `Id.run (Id.id true)`'s head is `Id.run`,
                    // an ordinary function, not a constructor) -- so the
                    // resolved `ind` may be entirely unrelated to the
                    // match's actual cases (`Id.run`'s cases are `true`/
                    // `false`, i.e. `Bool`, not `Id`). Cross-check against
                    // the cases themselves (same check `validate_match_
                    // constructors` re-runs for real just above this
                    // function's own caller) before committing to this
                    // preferred path; fall back to the pre-existing chain
                    // exactly as if `con_owner_name` had found nothing.
                    match validate_cases_against_inductive cases ind {
                        ok _ => ok (Option.some ind),
                        err _ => find_inductive_by_type_head_or_scan cases scrutinee_term scrutinee_typ scope,
                    },
                err _ => find_inductive_by_type_head_or_scan cases scrutinee_term scrutinee_typ scope,
            },
        Option.none => find_inductive_by_type_head_or_scan cases scrutinee_term scrutinee_typ scope,
    }

/// `find_inductive_for_cases`'s SECOND preference, after the new
/// `con_owner_name` check just above: the pre-existing `type_head_name`-
/// on-the-INFERRED-TYPE path, falling to `find_inductive_by_call_return_
/// type_or_scan` (the scrutinee's own call-head-return-type check, THEN
/// the ambiguous constructor-name scan) when it doesn't apply.
def find_inductive_by_type_head_or_scan (cases : List MatchCase) (scrutinee_term : Term) (scrutinee_typ : Term) (scope : Scope) : Result TypeError (Option Inductive) :=
    match type_head_name scrutinee_typ {
        Option.some id =>
            match scope_find_inductive (ModulePath.mp (List.cons id List.empty)) scope {
                ok ind => ok (Option.some ind),
                err _ => find_inductive_by_call_return_type_or_scan cases scrutinee_term scope,
            },
        Option.none => find_inductive_by_call_return_type_or_scan cases scrutinee_term scope,
    }

/// Third preferred path, tried before the ambiguous constructor-name
/// scan: when the scrutinee term is a call chain headed by a known
/// global def (`Term.app` chain bottoming out at `Term.var _ (named
/// id)`), resolve the inductive from THAT DEF'S OWN DECLARED return
/// type (`ScopeData.def_return_types`, populated from `Def.typ` --
/// deliberately NOT `ScopeDef.sig`, which stays unconditionally
/// `Term.hole` by its own load-bearing design, see `build_scope_def`'s
/// doc comment). `type_check_match`'s scrutinee is always checked in
/// pure INFER mode (`Term.hole` expected type) -- for a scrutinee
/// that's a bare function call, infer mode had NO way to recover the
/// call's return type at all before this (`extract_pi_ret` never sees a
/// real `Term.pi` for the callee, since `ScopeDef.sig` is hole), so
/// `match <a bare call> { <Ctor> args => ... }` (no outer annotation --
/// exactly `match fresh_temp c { CtxStrPair.mk ctx1 temp => ... }`'s own
/// shape) always fell straight through to the ambiguous scan below --
/// confirmed to silently return the WRONG field's value whenever two
/// inductives share that constructor name, not just fail to compile.
/// Every `struct`'s auto-generated constructor is always named `mk`
/// (`build_scope_struct`), so this was ambiguous between EVERY pair of
/// structs in the whole loaded corpus. Bare-name lookup only, matching
/// `type_head_name`'s own established convention just above -- a
/// dotted/cross-module call head is left to the existing fallback chain
/// unchanged, same "only ever ADD a strictly-better preferred path"
/// design this whole function already follows.
def find_inductive_by_call_return_type_or_scan (cases : List MatchCase) (scrutinee_term : Term) (scope : Scope) : Result TypeError (Option Inductive) :=
    match call_head_def_name scrutinee_term {
        Option.some id =>
            match scope_find_def_return_type (ModulePath.mp (List.cons id List.empty)) scope {
                Option.some ret_typ =>
                    match type_head_name ret_typ {
                        Option.some tid =>
                            match scope_find_inductive (ModulePath.mp (List.cons tid List.empty)) scope {
                                ok ind => ok (Option.some ind),
                                err _ => find_inductive_for_cases_by_constructor cases scope,
                            },
                        Option.none => find_inductive_for_cases_by_constructor cases scope,
                    },
                Option.none => find_inductive_for_cases_by_constructor cases scope,
            },
        Option.none => find_inductive_for_cases_by_constructor cases scope,
    }

/// Unwrap a `Term.app f a` chain to its head identifier, when that head
/// is a named global reference (`Term.var _ (DebugName.named id)`) --
/// mirrors `type_head_name`'s own identical unwrap just above, over the
/// scrutinee TERM (the call itself) instead of its inferred TYPE.
def call_head_def_name (t : Term) : Option Identifier :=
    match t {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => Option.some id,
                DebugName.unnamed => Option.none,
            },
        Term.app f _ => call_head_def_name f,
        _ => Option.none,
    }

/// Extract the qualifier prefix of a dotted name string (e.g.
/// `"Vec.cons" -> Option.some "Vec"`, `"cons" -> Option.none`) --
/// companion to `last_dotted_segment_go` above (same backward `.`-scan
/// idiom), returning the OTHER half of the split. `String.slice s 0 idx`
/// takes a LENGTH as its third argument (not an end index), so `idx`
/// (the '.' byte's own position) is exactly the right length to grab
/// everything strictly before it.
#[terminating]
def dotted_qualifier_go (s : String) (idx : I64) : Option String :=
    if I64.lt idx 0 then Option.none
    else
        match (String.get s idx : Option U8) {
            Option.some byte_val =>
                if U8.beq byte_val 46u8 then // '.' is ASCII 46
                    Option.some (String.slice s 0 idx)
                else
                    dotted_qualifier_go s (idx - 1),
            Option.none => Option.none
        }

def dotted_qualifier (s : String) : Option String :=
    dotted_qualifier_go s (String.length s - 1)

/// Find the `ModulePath` naming a scrutinee term's owning inductive,
/// directly from the term itself rather than its (often uninformative,
/// `Term.hole`-when-unannotated) inferred TYPE. Two cases:
///
/// - `Term.con c`: `c`'s own `typ_name` field names the owning inductive
///   DIRECTLY and unambiguously (`Con.mk cname typ_name num_args args`),
///   same field `type_check_con` itself already trusts for its own
///   preferred lookup (`scope_find_inductive typ_name scope`, `infer.mo`
///   ~1318). Kept for completeness / future-proofing, but **the parser
///   never actually constructs a `Term.con`** for ordinary
///   constructor-call syntax (confirmed: `grep -n "Term.con\|Con.mk"
///   lang/parser.mo` finds zero construction sites, only pattern-match
///   references) -- so in practice this arm doesn't fire yet.
/// - `Term.var _ (DebugName.named id)`: what a qualified constructor
///   reference like `Vec.cons` actually type-checks to
///   (`type_check_free_var_con` returns `Term.var sentinel dbg` with the
///   ORIGINAL, still-dotted `dbg` preserved) -- extract the dotted
///   qualifier ("Vec") from `id`'s own text via `dotted_qualifier` above
///   and treat it as a one-segment `ModulePath`. This is the arm that
///   actually fires for real qualified-constructor scrutinees.
///
/// Either way, a scrutinee's own TERM still names its constructor's
/// owner directly even when its inferred TYPE doesn't (a bare
/// constructor-application scrutinee with no outer annotation infers as
/// `Term.hole`, useless to `type_head_name`) -- so this is a strictly
/// NEW, more-preferred check, added ahead of the pre-existing
/// `type_head_name`/constructor-name-scan chain, which is otherwise
/// completely unchanged (per that chain's own established "only ever
/// ADD a strictly-better preferred path" design, see `find_inductive_
/// for_cases`'s prior doc comment) -- confirmed as the fix for a real
/// collision: `match Vec.cons 42 Vec.nil { cons h t => match t { nil =>
/// true } }` (no outer annotation) used to resolve the shared `cons`
/// name to `List` (declared first in `init/prelude.mo`) instead of
/// `Vec`, via the ambiguous scan this check now gets a chance to bypass.
def con_owner_name (t : Term) : Option ModulePath :=
    match t {
        Term.con c => match c { Con.mk _ typ_name _ _ => Option.some typ_name },
        Term.app f _ => con_owner_name f,
        Term.var _ dbg =>
            match dbg {
                DebugName.named id =>
                    match id {
                        Identifier.id s =>
                            match dotted_qualifier s {
                                Option.some qual => Option.some (ModulePath.mp (List.cons (Identifier.id qual) List.empty)),
                                Option.none => Option.none,
                            }
                    },
                DebugName.unnamed => Option.none,
            },
        _ => Option.none,
    }

/// The last-resort constructor-name-scan lookup -- still the correct
/// behavior when the scrutinee's own type isn't concretely known via any
/// of the preferred paths above, but now detects a genuine AMBIGUITY
/// (more than one inductive with a matching constructor name -- always
/// true between any two `struct`s, whose auto-generated constructor is
/// always `mk`) and fails loudly instead of silently returning whichever
/// candidate `HashMap.to_list`'s arbitrary bucket order finds first (see
/// `scope_find_all_inductives_by_constructor`'s own doc comment,
/// `lang/scope.mo`, for the confirmed-live silent-wrong-value repro this
/// closes). A single, unambiguous match still resolves exactly as
/// before.
def find_inductive_for_cases_by_constructor (cases : List MatchCase) (scope : Scope) : Result TypeError (Option Inductive) :=
    match cases {
        List.empty => ok Option.none,
        List.cons hd rest =>
            match hd {
                MatchCase.mc name _ _ _ =>
                    let wildcard_id : Identifier := Identifier.id "_" in
                    // A bare field-pattern case's own name is the parser's
                    // empty-string placeholder (`{ .. }`, `plans/
                    // implementations/struct-field-destructuring.md`'s Phase
                    // 6) -- it can never itself name a real constructor to
                    // scan by, so it's skipped here exactly like a wildcard,
                    // deferring entirely to a NAMED sibling case (or, if
                    // none exists in this match at all, to
                    // `resolve_field_pattern_case`'s own hard error once
                    // `type_check_field_pattern_case` runs with `maybe_ind
                    // = Option.none`).
                    if Similar.similar name wildcard_id || String.beq (show_identifier name) ""
                    then find_inductive_for_cases_by_constructor rest scope
                    else
                        let con_mp : ModulePath := ModulePath.mp (List.cons name List.empty) in
                        match scope_find_all_inductives_by_constructor con_mp scope {
                            List.empty => ok Option.none,
                            List.cons only more =>
                                match more {
                                    List.empty => ok (Option.some only),
                                    List.cons second _rest =>
                                        err (TypeError.custom (ambiguous_constructor_message name only second)),
                                },
                        },
            },
    }

/// Error text for `find_inductive_for_cases_by_constructor`'s new
/// ambiguity check -- names both colliding types so the diagnostic is
/// immediately actionable, not just "ambiguous, good luck".
def ambiguous_constructor_message (con_name : Identifier) (ind1 : Inductive) (ind2 : Inductive) : String :=
    "ambiguous constructor `" ++ show_identifier con_name ++ "`: could resolve to either `"
        ++ inductive_name_str ind1 ++ "` or `" ++ inductive_name_str ind2
        ++ "` here -- annotate the scrutinee's type, or bind it to a local first"

def inductive_name_str (ind : Inductive) : String :=
    match ind {
        Inductive.mk name _ _ _ _ _ => show_module_path name,
    }

/// Check that every non-wildcard case constructor exists in the
/// inductive. A field-pattern case (bare OR named) is skipped here --
/// deferred entirely to `resolve_field_pattern_case`'s own resolution in
/// `type_check_field_pattern_case`, which raises the same "unknown
/// constructor"-shaped error with a message specific to field patterns
/// (and, for the bare form, can't even be checked by name at all here).
def validate_cases_against_inductive (cases : List MatchCase) (ind : Inductive) : Result TypeError Bool :=
    match cases {
        List.empty => ok true,
        List.cons hd rest =>
            match hd {
                MatchCase.mc name _ _ fp =>
                    let wildcard_id : Identifier := Identifier.id "_" in
                    match fp {
                        Option.some _ => validate_cases_against_inductive rest ind,
                        Option.none =>
                            if Similar.similar name wildcard_id
                            then validate_cases_against_inductive rest ind
                            else
                                let con_mp : ModulePath := ModulePath.mp (List.cons name List.empty) in
                                if inductive_has_constructor ind con_mp
                                then validate_cases_against_inductive rest ind
                                else err (TypeError.custom "constructor not found in inductive"),
                    },
            },
    }

/// Type check match cases — process all cases and unify their body types.
def type_check_cases (cases : List MatchCase) (scrutinee_term : Term) (scrutinee_typ : Term) (maybe_ind : Option Inductive) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match type_check_cases_accum cases scrutinee_term scrutinee_typ maybe_ind expected_type scope local_types locals (Term.hole) List.empty {
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
def type_check_cases_accum (cases : List MatchCase) (scrutinee_term : Term) (scrutinee_typ : Term) (maybe_ind : Option Inductive) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) (acc_typ : Term) (acc_cases : List MatchCase) : Result TypeError CaseAcc :=
    match cases {
        List.cons hd rest =>
            match type_check_match_case hd scrutinee_term scrutinee_typ maybe_ind expected_type scope local_types locals {
                ok checked =>
                    match checked {
                        mk checked_case body_typ =>
                            let new_cases : List MatchCase := List.cons checked_case acc_cases in
                            match acc_typ {
                                Term.hole =>
                                    type_check_cases_accum rest scrutinee_term scrutinee_typ maybe_ind expected_type scope local_types locals body_typ new_cases,
                                _ =>
                                    match unify acc_typ body_typ {
                                        ok unified_typ =>
                                            type_check_cases_accum rest scrutinee_term scrutinee_typ maybe_ind expected_type scope local_types locals unified_typ new_cases,
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

/// Type check a single match case arm. A `field_pattern: Option.some`
/// case (`{ x, y } => ...`/`ConsName { x, y } => ...`,
/// `plans/implementations/struct-field-destructuring.md`'s Phase 6)
/// gets its own dedicated path (`type_check_field_pattern_case`) --
/// unlike the ordinary positional cases below, everything about it
/// (which constructor, which declared field order) still needs
/// resolving here; nothing about it can be trusted as already correct
/// the way a written positional case's `args` order is.
def type_check_match_case (case_ : MatchCase) (scrutinee_term : Term) (scrutinee_typ : Term) (maybe_ind : Option Inductive) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError CheckedCase :=
    match case_ {
        MatchCase.mc name args body fp =>
            match fp {
                Option.some field_pattern =>
                    type_check_field_pattern_case name args body field_pattern maybe_ind expected_type scope local_types locals,
                Option.none =>
                    let wildcard_id : Identifier := Identifier.id "_" in
                    if Similar.similar name wildcard_id then
                        match args {
                            List.empty =>
                                type_check_case_body_checked name args body expected_type scope local_types locals,
                            _ =>
                                err (TypeError.custom "wildcard pattern cannot bind arguments"),
                        }
                    else
                        match args {
                            List.empty =>
                                type_check_case_body_checked name args body expected_type scope local_types locals,
                            _ =>
                                let arg_types : List Term := arg_types_for_case name maybe_ind scrutinee_typ in
                                let extended_types : List Term := prepend_typed args arg_types local_types in
                                let extended_locals : LocalScope := prepend_typed_local_vars args arg_types locals in
                                type_check_case_body_checked name args body expected_type scope extended_types extended_locals,
                        },
            },
    }

// ─── Field-pattern match-case elaboration (`plans/implementations/
// struct-field-destructuring.md`'s Phase 7) ────────────────────────────
//
// Unlike the Rust reference (`core/src/core_check.rs`), this checker
// builds the checked term directly, in one pass, as it goes -- there is
// no `check`/`infer`-vs-`desugar_struct_literals` split here needing a
// SECOND independent hook (see `type_check_match_case`'s own doc
// comment); this one hook is where a field-pattern case's target
// constructor, field order, AND the body's own de-Bruijn retargeting
// (`term_permute`, `lang/typecheck/subst.mo`) all get resolved together.

/// Resolved shape of a field-pattern match case: the real constructor
/// name (never `case_`'s own possibly-empty bare-form name), its
/// declared field names/types (in DECLARED order -- what
/// `prepend_typed`/`prepend_typed_local_vars` need to build the correct
/// local scope for the case body), and `written_to_declared` (parallel
/// to the pattern's own written fields: `written_to_declared[w]` is the
/// declared-order position written slot `w` fills) -- what
/// `term_permute` needs to retarget the ALREADY-PARSED body.
struct ResolvedFieldPattern {
    resolved_name : Identifier,
    declared_names : List Identifier,
    declared_types : List Term,
    written_to_declared : List I64,
}

// `body` gets replaced with `permuted_body` (a TRANSFORMED term, not a
// structural subterm) before the final call into
// `type_check_case_body_checked` -- which, like this function's own
// sibling `type_check_match_case`'s positional path, is part of this
// checker's ordinary mutual recursion through `type_check`/nested
// matches, just no longer structurally obvious to the termination
// checker once the body is rebuilt in between. Well-founded regardless:
// `type_check_case_body_checked` only ever recurses on `body`'s own
// (unchanged-in-size) subterms from there, same as any other case.
#[terminating]
def type_check_field_pattern_case (name : Identifier) (args : List Identifier) (body : Term) (fp : FieldPattern) (maybe_ind : Option Inductive) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError CheckedCase :=
    match resolve_field_pattern_case name fp maybe_ind {
        err e => err e,
        ok resolved =>
            match resolved {
                mk resolved_name declared_names declared_types written_to_declared =>
                    let old_n : I64 := List.length args in
                    let new_n : I64 := List.length declared_names in
                    let old_depths : List I64 := old_depths_of written_to_declared old_n 0 in
                    let new_depths : List I64 := List.map (fn d => new_n - 1 - d) written_to_declared in
                    let permuted_body : Term := term_permute old_n new_n old_depths new_depths body in
                    let extended_types : List Term := prepend_typed declared_names declared_types local_types in
                    let extended_locals : LocalScope := prepend_typed_local_vars declared_names declared_types locals in
                    // The ELABORATED `MatchCase`'s own `args` (what codegen's
                    // `bind_match_fields`/`free_names_of_cases` actually bind
                    // names against -- see their own doc comments,
                    // `lang/codegen/emit.mo`) must be the WRITTEN BINDER
                    // names (`{ term := body }`'s `body`), NOT `declared_
                    // names` (`term`, the struct's own canonical field name)
                    // -- `body`'s own embedded `Term.var` references are
                    // untouched by `term_permute` (a pure de-Bruijn-index
                    // permutation, never touches a `Term.var`'s `dbg`), so
                    // they still say "body" throughout. Passing
                    // `declared_names` here left `args`/the body's own
                    // variable references silently DISJOINT for any RENAMED
                    // field (a punned field like `name` is unaffected --
                    // written binder == declared name coincidentally) --
                    // codegen's `ctx_lookup_local` for "body" then always
                    // failed, silently falling back to treating it as an
                    // unresolved GLOBAL 0-arg call (`@body()`), confirmed
                    // via a minimal repro and traced all the way from an
                    // `llc: undefined value '@body'` self-compile failure
                    // (`elaborate_def_with_scope`'s own `{ name, typ, term
                    // := body, ... }` param). `declared_order_binders`
                    // reorders `fp`'s own written binder names into the
                    // same DECLARED position order `args` must be in for
                    // `bind_match_fields`'s positional `monad_get_field`
                    // extraction to line up -- falling back to a declared
                    // field's own name only for a `..`-discarded, never-
                    // written position (unreachable in `body` by
                    // construction, so what it's bound to there doesn't
                    // matter for correctness, just needs to be SOME valid
                    // identifier).
                    let declared_binders : List Identifier := declared_order_binders declared_names fp in
                    type_check_case_body_checked resolved_name declared_binders permuted_body expected_type scope extended_types extended_locals,
            },
    }

/// See `type_check_field_pattern_case`'s own doc comment above for why
/// this exists -- reorders a `FieldPattern`'s written `(field, binder)`
/// entries into DECLARED-field-order binder names, falling back to each
/// declared field's own canonical name for a position no written entry
/// covers (only reachable via a trailing `..`).
#[partial]
def declared_order_binders (declared_names : List Identifier) (fp : FieldPattern) : List Identifier :=
    match fp {
        FieldPattern.mk entries _rest => declared_order_binders_go declared_names entries,
    }

#[partial]
def declared_order_binders_go (declared_names : List Identifier) (entries : List FieldPatternEntry) : List Identifier :=
    match declared_names {
        List.empty => List.empty,
        List.cons dn rest_dn =>
            let binder : Identifier := binder_for_declared_field entries dn in
            List.cons binder (declared_order_binders_go rest_dn entries),
    }

#[partial]
def binder_for_declared_field (entries : List FieldPatternEntry) (declared_name : Identifier) : Identifier :=
    match entries {
        List.empty => declared_name,
        List.cons e rest =>
            match e {
                FieldPatternEntry.mk field binder =>
                    if id_eq field declared_name then binder else binder_for_declared_field rest declared_name,
            },
    }

/// `old_depths_of`'s OWN elements never come from `written_to_declared`'s
/// VALUES, only its LENGTH+position (`old_n - 1 - w`, mirroring
/// `core_term::permute_binders`' own depth arithmetic: the LAST-written
/// field ends up innermost/depth-0, matching `lang/lower_core_ir.mo`'s
/// "fields pushed in declaration order" runtime convention) -- a plain
/// `List.map` can't express this (the mapper only sees each element's
/// VALUE, never its position), so this is genuine positional recursion,
/// not an ad hoc stand-in for an existing generic op.
#[partial]
def old_depths_of (written_to_declared : List I64) (old_n : I64) (w : I64) : List I64 :=
    match written_to_declared {
        List.empty => List.empty,
        List.cons _ rest => List.cons (old_n - 1 - w) (old_depths_of rest old_n (w + 1)),
    }

/// Resolve `case_name`/`fp` against `maybe_ind`: pick the target
/// constructor (the scrutinee inductive's SOLE constructor for a bare
/// pattern -- `case_name`'s own string is empty, the parser's
/// placeholder, see `lang/parser.mo`'s `match_case_try_bare_field_pattern`
/// -- or `case_name` directly for a named one), require every one of
/// its params to be named, and match the pattern's written fields
/// against the constructor's declared ones -- unknown field, duplicate
/// field, and (without a trailing `..`) an uncovered field are all real
/// errors here, not soft failures, matching every other `TypeError` this
/// checker already raises for a malformed program. `maybe_ind` being
/// `Option.none` (the scrutinee's type genuinely isn't known at all) is
/// also a hard error here -- unlike an ordinary positional case (which
/// tolerates it by falling back to `Term.hole` field types), a
/// field-pattern case has no way to resolve field order at all without
/// a real inductive to resolve against.
def resolve_field_pattern_case (case_name : Identifier) (fp : FieldPattern) (maybe_ind : Option Inductive) : Result TypeError ResolvedFieldPattern :=
    match maybe_ind {
        Option.none => err (TypeError.custom "cannot resolve `{ .. }`: the matched value's type isn't known here"),
        Option.some ind =>
            if String.beq (show_identifier case_name) "" then
                resolve_bare_field_pattern fp ind
            else
                match find_constructor_in_inductive ind (ModulePath.mp (List.cons case_name List.empty)) {
                    Option.none => err (TypeError.custom "unknown constructor in field pattern"),
                    Option.some ctor => resolve_field_pattern_against_constructor case_name ctor fp,
                },
    }

/// `{ .. }` (no constructor name) requires the scrutinee's inductive to
/// have EXACTLY one constructor -- mirrors the Rust reference's own
/// `resolve_field_pattern_case` (`core/src/core_check.rs`) bare-form
/// handling exactly.
def resolve_bare_field_pattern (fp : FieldPattern) (ind : Inductive) : Result TypeError ResolvedFieldPattern :=
    match ind {
        mk _ _ _ ctors _ _ =>
            match ctors {
                List.empty => err (TypeError.custom "`{ .. }` requires exactly one constructor; this type has none"),
                List.cons only rest =>
                    match rest {
                        List.empty =>
                            match only { InductConstructor.mk con_mp _ _ => resolve_field_pattern_against_constructor (constructor_bare_name con_mp) only fp },
                        List.cons _ _ =>
                            err (TypeError.custom "`{ .. }` requires exactly one constructor, but this type has several; use `ConsName { .. }` instead"),
                    },
            },
    }

/// The bare (last-segment) `Identifier` of a constructor's own
/// `ModulePath` -- `InductConstructor.mk`'s `name` is never
/// type-prefixed (see e.g. `arg_types_for_case`'s own doc comment).
/// `List.last` (`init/prelude.mo`) already covers "get the last
/// element"; `Option.none` (an empty `ModulePath`) shouldn't happen for
/// a real constructor, handled defensively with an empty-string
/// placeholder rather than assumed impossible.
#[partial]
def constructor_bare_name (mp : ModulePath) : Identifier :=
    match mp {
        ModulePath.mp ids =>
            match List.last ids {
                Option.some last_id => last_id,
                Option.none => Identifier.id "",
            },
    }

// NOTE: unlike `arg_types_for_case`'s positional-pattern sibling (see its
// own doc comment, `substitute_inductive_type_params`), `declared_types`
// below is NOT substituted against the scrutinee's actual type
// arguments -- a field-pattern case (`{ x, y } => ...`) over a GENERIC
// inductive would bind its field vars to the raw, uninstantiated
// declared param types, same latent bug `arg_types_for_case` had before
// its fix. Not touched here: no confirmed failure in the corpus exercises
// this path with a generic scrutinee (fast sweep + full `slow_tests/
// typecheck_init_tests.mo` both green without it), and wiring `scrutinee_
// typ` through here would also need threading it through `resolve_field_
// pattern_case`/`resolve_bare_field_pattern`. Flagged as a known,
// unconfirmed gap rather than spending the extra signature-threading on
// a path with no observed break.
def resolve_field_pattern_against_constructor (resolved_name : Identifier) (ctor : InductConstructor) (fp : FieldPattern) : Result TypeError ResolvedFieldPattern :=
    match ctor {
        InductConstructor.mk _ params _ =>
            if params_all_named params then
                match fp {
                    FieldPattern.mk entries rest =>
                        let declared_names : List Identifier := param_names params in
                        match resolve_entries_against_params entries declared_names {
                            err e => err e,
                            ok written_to_declared =>
                                if Bool.not rest && Bool.not (I64.beq (List.length written_to_declared) (List.length declared_names))
                                then err (TypeError.custom "field pattern is missing field(s) (add `..` to discard them)")
                                else ok ({
                                    resolved_name := resolved_name,
                                    declared_names := declared_names,
                                    declared_types := types_from_params params,
                                    written_to_declared := written_to_declared,
                                }),
                        },
                }
            else
                err (TypeError.custom "constructor has an unnamed field; use the positional pattern instead of a field pattern"),
    }

// `params_all_named`/`param_names`/`i64_list_contains` below are hand-
// rolled recursion, NOT `List.all`/`List.map`/`List.contains` -- tried
// the generic versions first, but confirmed (via a minimal reproduction:
// a trivial NEW cross-module function whose only body is `List.map (fn
// n => n + 1) xs` fails the exact same way) that a brand-new top-level
// function DEFINED IN THIS MODULE that calls a generic `{A : Type}`
// `List.*` op internally fails at RUNTIME with `unresolved global`, even
// though the identical `List.map`/`List.all` call written INLINE at a
// call site works fine -- the same class of pre-existing self-hosted
// evaluator limitation `lang/types.mo`'s own `use std.map {}` comment
// already documents for a nullary class method (`Map.empty`), just
// manifesting for an ordinary generic list op instead of a class method
// this time. The `Map.empty` bug's own documented workaround (adding an
// empty `use` of the defining module) does NOT fix this one -- tried it
// here first; it left `params_all_named` still unresolved AND broke
// unrelated arithmetic (`unresolved global: HAdd.add`) elsewhere in this
// file's own test suite. Hand-rolled recursion sidesteps the bug
// entirely and is what the rest of this file already does for the same
// shape of operation (e.g. `types_from_params`, just above
// `arg_types_for_case`) -- not a style regression, just consistent with
// existing precedent once the generic path is confirmed broken.
def params_all_named (params : List Param) : Bool :=
    match params {
        List.empty => true,
        List.cons p rest =>
            match p { Param.mk pname _ _ _ _ => Bool.not (String.beq (show_identifier pname) "") && params_all_named rest },
    }

def param_names (params : List Param) : List Identifier :=
    match params {
        List.empty => List.empty,
        List.cons p rest => match p { Param.mk pname _ _ _ _ => List.cons pname (param_names rest) },
    }

/// For each written entry (in order), find its declared position --
/// unknown-field and duplicate-field are both real errors here.
def resolve_entries_against_params (entries : List FieldPatternEntry) (declared_names : List Identifier) : Result TypeError (List I64) :=
    resolve_entries_against_params_go entries declared_names List.empty

#[partial]
def resolve_entries_against_params_go (entries : List FieldPatternEntry) (declared_names : List Identifier) (used : List I64) : Result TypeError (List I64) :=
    match entries {
        List.empty => ok List.empty,
        List.cons e rest =>
            match e {
                FieldPatternEntry.mk field _binder =>
                    match index_of_identifier field declared_names 0 {
                        Option.none => err (TypeError.custom "field pattern names a field the constructor doesn't have"),
                        Option.some idx =>
                            if i64_list_contains idx used
                            then err (TypeError.custom "field listed more than once in field pattern")
                            else
                                match resolve_entries_against_params_go rest declared_names (List.cons idx used) {
                                    err e2 => err e2,
                                    ok rest_idxs => ok (List.cons idx rest_idxs),
                                },
                    },
            },
    }

/// See `params_all_named`'s own doc comment above for why this is
/// hand-rolled recursion rather than `List.contains` -- `std/list.mo`'s
/// own `List.contains` is ALSO commented out there, independently,
/// pending a separate documented instance-resolution bug -- so it was
/// never a real option here regardless.
#[partial]
def i64_list_contains (target : I64) (xs : List I64) : Bool :=
    match xs {
        List.empty => false,
        List.cons hd rest => if I64.beq target hd then true else i64_list_contains target rest,
    }

/// No generic "find index" op exists in this codebase's `List` module
/// (`std/list.mo`'s own `List.contains` is commented out pending a
/// separate, pre-existing instance-resolution bug -- see that file) --
/// this is genuine custom recursion, not a stand-in for one.
#[partial]
def index_of_identifier (target : Identifier) (names : List Identifier) (i : I64) : Option I64 :=
    match names {
        List.empty => Option.none,
        List.cons hd rest =>
            if id_eq target hd then Option.some i else index_of_identifier target rest (i + 1),
    }

/// The matching constructor's OWN declared field types, in declared
/// order, when `maybe_ind` (the inductive this whole match's cases
/// were resolved against -- `validate_match_constructors`, above) is
/// known and actually has a constructor by this case's name.
/// `List.empty` otherwise (no inductive known at all, or -- shouldn't
/// happen for an already-validated case, but handled safely regardless
/// -- no matching constructor found in it): `prepend_typed`/
/// `rec_prepend_typed_local_vars` below both treat a too-short (here,
/// empty) type list as "fall back to `Term.hole`", exactly matching
/// this function's own previous unconditional behavior. Fixes a real
/// bug: a pattern-bound variable from an OUTER match (e.g. `ctors` in
/// `match info { type_info _ ctors => match ctors { cons c tail =>
/// ..., empty => ... } }`) used to always get `Term.hole` regardless
/// of its real declared type -- so a NESTED match on it could never
/// use `find_inductive_for_cases`'s preferred exact-type-lookup path,
/// always falling back to the ambiguous constructor-name-only scan
/// instead. That scan is only really safe when at most one visible
/// inductive has a given constructor name -- `List`/`Vec` (both
/// declare a bare `cons`) already collide on it for real
/// (`init/prelude.mo`), so the fallback can and does pick the wrong
/// one whenever it's reached avoidably. Propagating the real type here
/// removes one whole class of avoidable fallback-scan hits without
/// touching the scan itself (which a previous, reverted attempt at a
/// scan-order fix already showed is not safe to change directly -- see
/// `find_inductive_for_cases`'s own doc comment above).
def arg_types_for_case (case_name : Identifier) (maybe_ind : Option Inductive) (scrutinee_typ : Term) : List Term :=
    match maybe_ind {
        Option.some ind =>
            let con_mp : ModulePath := ModulePath.mp (List.cons case_name List.empty) in
            match find_constructor_in_inductive ind con_mp {
                Option.some ctor =>
                    match ctor { InductConstructor.mk _ params _ =>
                        substitute_inductive_type_params ind scrutinee_typ (types_from_params params)
                    },
                Option.none => List.empty,
            },
        Option.none => List.empty,
    }

/// Substitute an inductive's own declared type PARAMETERS (`A` in `type
/// Option A { some (a: A), none }`) throughout a list of constructor
/// field types with the scrutinee's ACTUAL type arguments (`ParseError`,
/// from a concrete scrutinee of type `Option ParseError`) -- without
/// this, a generic constructor's field binder (`e` in `some e => e`)
/// gets bound to the raw, uninstantiated parameter name (`A`, a bare
/// free-name `Term.var`) instead of its real instantiated type. That
/// only ever unified successfully by accident before -- against `unify`'s
/// universal `Term.hole` wildcard -- since every match-arm body reached
/// from an ordinary top-level def's own outer `expected_type` was always
/// `Term.hole` until `check_def_with_scope` (`lang/module.mo`) started
/// threading a def's real declared return type through; confirmed via a
/// minimal repro (`Option ParseError`'s `some e => e` arm regressing
/// `lang/parser/combinators.mo`'s `alt_fold_best_or_default`, "type
/// mismatch: expected A, found ParseError", once that threading landed).
///
/// `ind`'s own `params` are positionally zipped against `scrutinee_typ`'s
/// application spine (`flatten_call_spine`, `lang.scope`) -- e.g.
/// `Option ParseError` flattens to head `Option`, args `[ParseError]`,
/// zipped 1:1 against `Option`'s own single declared param `A`. Reuses
/// `name_subst_term` (`lang.typecheck.name_subst`) wholesale rather than
/// writing a new substitution walker: that module's own "ordinary free
/// `Term.var sentinel (DebugName.named X)` reference" target shape is
/// exactly what an inductive's own param appears as inside its
/// constructors' field types (skolemized during the inductive's own
/// check, never de-Bruijn-bound there). A too-short (or absent, `maybe_
/// ind = Option.none` upstream) argument spine just substitutes fewer
/// params, matching every other partial-information fallback in this
/// file rather than erroring.
def substitute_inductive_type_params (ind : Inductive) (scrutinee_typ : Term) (field_types : List Term) : List Term :=
    match ind {
        Inductive.mk _ params _ _ _ _ =>
            match flatten_call_spine scrutinee_typ {
                CallSpine.mk _head actual_args =>
                    substitute_inductive_type_params_go params actual_args field_types
            },
    }

// Hand-rolled recursion, not `List.map`/`List.zip` -- mirrors `types_
// from_params`/`param_names`'s own established precedent in this file
// (see the doc comment just above `arg_types_for_case`) for a
// brand-new top-level function calling a generic `List.*` op.
#[terminating]
def substitute_inductive_type_params_go (params : List Param) (actual_args : List Term) (field_types : List Term) : List Term :=
    match params {
        List.cons p prest =>
            match actual_args {
                List.cons a arest =>
                    match p {
                        Param.mk pname _ _ _ _ =>
                            substitute_inductive_type_params_go prest arest (name_subst_over_list pname a field_types)
                    },
                List.empty => field_types,
            },
        List.empty => field_types,
    }

#[terminating]
def name_subst_over_list (target : Identifier) (replacement : Term) (types : List Term) : List Term :=
    match types {
        List.cons t rest => List.cons (name_subst_term target replacement t) (name_subst_over_list target replacement rest),
        List.empty => List.empty,
    }

/// Just the `type_` field of each `Param`, in order.
def types_from_params (params : List Param) : List Term :=
    match params {
        List.cons p rest =>
            match p { Param.mk _ typ _ _ _ => List.cons typ (types_from_params rest) },
        List.empty => List.empty,
    }

/// Prepend one type per identifier onto the front of `local_types` --
/// `arg_types` (matching `args`, in the same order) when available,
/// falling back to `Term.hole` for any identifier `arg_types` runs out
/// before reaching (this is what makes an empty/too-short `arg_types`
/// behave EXACTLY like the old `prepend_holes` it replaces).
def prepend_typed (args : List Identifier) (arg_types : List Term) (local_types : List Term) : List Term :=
    match args {
        List.cons x rest =>
            match arg_types {
                List.cons t trest => prepend_typed rest trest (List.cons t local_types),
                List.empty => prepend_typed rest List.empty (List.cons Term.hole local_types),
            },
        List.empty => local_types,
    }

/// Prepend LocalVar bindings onto `locals` -- same `arg_types`/
/// `Term.hole`-fallback pairing as `prepend_typed` above.
def prepend_typed_local_vars (args : List Identifier) (arg_types : List Term) (locals : LocalScope) : LocalScope :=
    let new_vars : List LocalVar := rec_prepend_typed_local_vars args arg_types in
    { vars := new_vars, parent := Option.some locals }

/// Recursively build a list of LocalVar entries from identifiers, paired
/// with `arg_types` (falling back to `Term.hole` once it runs out).
def rec_prepend_typed_local_vars (args : List Identifier) (arg_types : List Term) : List LocalVar :=
    match args {
        List.cons x rest =>
            match arg_types {
                List.cons t trest =>
                    let lv : LocalVar := { name := x, typ := t, multiplicity := Multiplicity.many } in
                    List.cons lv (rec_prepend_typed_local_vars rest trest),
                List.empty =>
                    let lv : LocalVar := { name := x, typ := Term.hole, multiplicity := Multiplicity.many } in
                    List.cons lv (rec_prepend_typed_local_vars rest List.empty),
            },
        List.empty => List.empty,
    }

/// Type-check the body of a match case arm, returning the checked result.
// `expected_type`: the ENCLOSING match's own expected type (from
// `type_check_match`'s caller), not the per-case cross-consistency
// `acc_typ` `type_check_cases_accum` unifies separately below -- those
// are two different mechanisms. Threaded through so a case body that
// genuinely NEEDS outside type information to check at all (a struct
// literal with no `: StructName` self-annotation, e.g. `match pt { mk _
// y => { x := new_x, y := y } }` where only the enclosing `def`'s own
// declared return type says which struct) has somewhere to get it from,
// instead of unconditionally checking every case body in pure-infer
// mode (`Term.hole`) regardless of context -- confirmed as the root
// cause of `init/optics_tests.mo`'s `set_x`/`set_y` failing with
// "cannot infer struct type... no expected type from context" (fixed
// 2026-08-25). Still `Term.hole` in the overwhelming common case (a
// match with no informative outer expected type at all), so this is a
// strict widening, not a behavior change, for every case that doesn't
// need it.
def type_check_case_body_checked (name : Identifier) (args : List Identifier) (body : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError CheckedCase :=
    match type_check body expected_type scope local_types locals {
        ok body_tt =>
            let body_term : Term := tt_term body_tt in
            let body_typ : Term := tt_typ body_tt in
            let no_fp : Option FieldPattern := Option.none in
            let new_case : MatchCase := MatchCase.mc name args body_term no_fp in
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
/// expected type starts as `Term.hole` (any match-arm body reached from
/// a call site that itself has no informative expected type -- as of
/// 2026-08-25 `type_check_case_body_checked` CAN thread a real outer
/// expected type through when one is available, but `check_def_with_
/// scope`'s own top-level call still always passes `Term.hole` for a
/// def's body, so this remains the overwhelmingly common case in
/// practice today). Trusting `expected_type` directly matches
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
                    // A qualified class-method reference (`Foldable.foldr`)
                    // is stored under its bare method name only
                    // (`add_methods_go`) -- strip to the last dotted
                    // segment before looking it up, mirroring
                    // `type_check_free_var_con`'s identical existing fix
                    // just below for qualified constructor references.
                    let bare_id : Identifier := match id { Identifier.id s => Identifier.id (last_dotted_segment s) } in
                    let clsd_result : Result ScopeError ScopeClassDef := scope_find_class_def_by_name bare_id scope in
                    match clsd_result {
                        ok cd =>
                            match resolve_class_method cd expected_type scope locals {
                                ok tt => ok tt,
                                err _ =>
                                    // Fall back to the class method's own
                                    // abstract signature (not resolved) --
                                    // e.g. a heterogeneous/multi-param
                                    // class `carrier_from_expected_type`
                                    // deliberately doesn't cover, or an
                                    // operand whose real type this pure-
                                    // infer-mode checker can't recover
                                    // (`ScopeDef.sig` is always `Term.hole`
                                    // for an ordinary global, by existing,
                                    // documented design -- `lang.scope`'s
                                    // `build_scope_def` -- so a class-
                                    // method carrier derived purely from
                                    // bidirectional propagation can't see
                                    // through an ordinary function call in
                                    // an otherwise-uninformative context;
                                    // `lang.scope`'s own syntactic
                                    // `resolve_class_calls_decls` pass,
                                    // which every codegen path still runs
                                    // after this, covers that case
                                    // instead via `infer_carrier_type`'s
                                    // own declared-return-type lookup).
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

/// Type check a function application. Named-call fallback (`plans/
/// implementations/named-field-construction.md`, Phase 5): if checking
/// `a` against its own expected type fails outright, and `a` is an
/// UNANNOTATED struct literal, try reinterpreting the whole `App` as a
/// named call against `f`'s own declared params instead
/// (`type_check_named_call`) before giving up with the ORIGINAL error.
/// Note this trigger condition is broader here than the reference
/// compiler's own (`core_check.rs`'s `try_desugar_named_call`, only tried
/// on a hard type-check FAILURE): `type_check`ing `a` against `Term.hole`
/// (this checker's usual "no information" expected type for an ordinary
/// named callee -- `app_arg_expected_type` only ever returns something
/// else for an inline `Term.lam`, see its own doc comment) ALREADY fails
/// for any unannotated struct literal today (`type_check_struct_lit`
/// requires either a self-annotation or a concrete `expected_type` head
/// name, and `Term.hole` has neither) -- so in practice this fallback is
/// reached for every unannotated-struct-literal-argument call to an
/// ordinary named function/constructor, not just ones that were
/// previously hard errors. This is a strict improvement, not a behavior
/// change: no program with this shape type-checked successfully before
/// (confirmed: this is the exact gap noted in that plan's own Current
/// State investigation of this file), so there is nothing to preserve.
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
        err e =>
            match named_call_fields_of a {
                Option.none => err e,
                Option.some fields =>
                    match type_check_named_call f fields expected_type scope local_types locals {
                        err e2 => err e2,
                        ok result => match result {
                            Option.some tt => ok tt,
                            Option.none => err e,
                        },
                    }
            },
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
                                ok elab_args => ok (mk_typed (Term.con (Con.mk cname typ_name num_args elab_args)) expected_type),
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
                                                    ok elab_args => ok (mk_typed (Term.con (Con.mk cname typ_name num_args elab_args)) expected_type),
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
                                                ok elab_args =>
                                                    let mk_name : Identifier := struct_lit_con_name con_name in
                                                    let c : Con := Con.mk mk_name typ_mp (List.length params) elab_args in
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
///
/// A field OMITTED from the literal falls back to its own declared
/// DEFAULT expression (`Param`'s own `default : Option Term`, `lang/
/// types.mo`) when the struct declares one -- previously discarded
/// entirely (`Param.mk pname _ _ _ _`), always producing `Option.none`
/// for any omitted field regardless of whether a default existed.
/// `codegen`'s `lower_sparse_args` (`lang/lower_core_ir.mo`) lowers a
/// constructor's args left-to-right and STOPS at the first `Option.
/// none` hole -- correct for a genuinely under-saturated constructor
/// call, but a struct literal that legitimately omits a DEFAULTED field
/// (not a real "hole") needs that field's value actually present, not a
/// hole codegen will truncate the whole allocation at. Confirmed live
/// via a real self-compiled binary's own SIGSEGV: `lang/scope.mo`'s
/// `scope_data_empty` (a 9-field `ScopeData`, 2 of which --
/// `def_params`/`def_return_types` -- are declared with defaults and
/// omitted from the literal) compiled to `alloc_constructor(318, 7)`,
/// silently allocating only 7 fields' worth of space -- any later
/// `monad_get_field`/`monad_set_field` on field 7 or 8 read/wrote past
/// the end of the allocation.
#[terminating]
def struct_lit_build_args (params : List Param) (fields : List StructLitField) : List (Option Term) :=
    match params {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Param.mk pname _ _ pdefault _ =>
                    let found := struct_lit_find_field fields pname in
                    let val := match found {
                        Option.some _ => found,
                        Option.none => pdefault,
                    } in
                    List.cons val (struct_lit_build_args rest fields)
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

// -----------------------------------------------------------------------
// Phase 5 of `plans/implementations/named-field-construction.md`:
// constructor-target named calls (`NAME { field := value, ... }`,
// order-independent keyword arguments matched against `NAME`'s own
// declared constructor params). Generalizes `type_check_struct_lit`'s
// existing machinery (hardcoded to "the struct's SOLE constructor",
// resolved from a TYPE) to "a specific named constructor of ANY
// inductive", resolved from a NAME (`f`) instead -- reusing
// `scope_find_inductive_by_constructor`/`find_constructor_in_inductive`
// (already general, see `type_check_free_var_con` above) and
// `check_con_args_against_params` (already checks, not infers, each
// present field against its declared type -- no analogous check-vs-infer
// gap to fix here the way the Rust reference's `infer`'s own `Con` arm
// needed one, see that plan's Phase 1).
// -----------------------------------------------------------------------

/// If `a` is an UNANNOTATED struct literal (`type_name = Option.none` --
/// an explicit `: StructName` annotation always means "build this
/// struct," never "spread across NAME's own params", matching the
/// reference's identical rule), its fields; `Option.none` otherwise
/// (including for an ANNOTATED struct literal, or any other term shape).
def named_call_fields_of (a : Term) : Option (List StructLitField) :=
    match a {
        Term.lit lit_val =>
            match lit_val {
                Literal.struct_lit fields type_name =>
                    match type_name {
                        Option.none => Option.some fields,
                        Option.some _ => Option.none,
                    },
                _ => Option.none,
            },
        _ => Option.none,
    }

/// `Inductive.mk`'s own `name` field, bare-last-segment only -- mirrors
/// `struct_lit_con_name`'s identical extraction for a CONSTRUCTOR's own
/// `ModulePath`, just applied to the owning inductive's instead. Used to
/// build a resolved named call's own result type (`Term.var sentinel
/// (DebugName.named ...)`), the same shape `type_check_struct_lit`
/// returns for an explicitly-annotated literal.
def inductive_bare_name (ind : Inductive) : Identifier :=
    match ind {
        Inductive.mk name _ _ _ _ _ =>
            match name {
                ModulePath.mp ids =>
                    match list_last ids {
                        Option.some id => id,
                        Option.none => Identifier.id "?",
                    }
            }
    }

def inductive_module_path (ind : Inductive) : ModulePath :=
    match ind {
        Inductive.mk name _ _ _ _ _ => name,
    }

/// Whether `name` is among `params`' own declared names.
#[terminating]
def named_call_param_exists (params : List Param) (name : Identifier) : Bool :=
    match params {
        List.empty => false,
        List.cons p rest =>
            match p {
                Param.mk pname _ _ _ _ =>
                    if id_eq pname name then true else named_call_param_exists rest name
            }
    }

/// Every literal field name must be among `params`' own declared names --
/// STRICTER than `struct_lit_build_args`'s existing leniency (which
/// silently drops an unmatched literal field, since it only ever walks
/// the STRUCT's own declared fields, never the literal's) -- a genuine
/// named call should reject a typo'd field name outright rather than
/// silently ignore it.
#[terminating]
def named_call_check_unknown_fields (params : List Param) (fields : List StructLitField) : Result TypeError Bool :=
    match fields {
        List.empty => ok true,
        List.cons f rest =>
            match f {
                StructLitField.mk fname _ =>
                    if named_call_param_exists params fname
                    then named_call_check_unknown_fields params rest
                    else err (TypeError.custom (String.concat "named call: unknown field `" (String.concat (show_identifier fname) "`")))
            }
    }

/// Every declared param must be covered by a literal field -- no default
/// mechanism exists for a `lang/` constructor of ANY kind (ordinary
/// `type` or `struct`) today, so this is always required (matches the
/// reference's own finding: `Inductive.defaults` has no `lang/`
/// equivalent at all).
#[terminating]
def named_call_check_missing_fields (params : List Param) (fields : List StructLitField) : Result TypeError Bool :=
    match params {
        List.empty => ok true,
        List.cons p rest =>
            match p {
                Param.mk pname _ _ _ _ =>
                    match struct_lit_find_field fields pname {
                        Option.some _ => named_call_check_missing_fields rest fields,
                        Option.none => err (TypeError.custom (String.concat "named call: missing required field `" (String.concat (show_identifier pname) "`"))),
                    }
            }
    }

def named_call_validate_fields (params : List Param) (fields : List StructLitField) : Result TypeError Bool :=
    match named_call_check_unknown_fields params fields {
        err e => err e,
        ok _ => named_call_check_missing_fields params fields,
    }

/// Resolves `f` (the callee) as a constructor name and, if found, builds
/// the reordered `Term.con`. Returns `ok Option.none` when the shape
/// doesn't apply at all (`f` isn't a bare named variable, or it doesn't
/// resolve to a known constructor -- Phase 6 tries an ordinary `def`'s
/// own params next, once that infrastructure lands) -- callers fall back
/// to the ORIGINAL `type_check_app` error in that case. Returns `err`
/// once `f` DOES resolve to a real constructor but field validation
/// itself fails (unknown/missing field, a field value's own type
/// mismatch) -- callers surface THAT error directly instead, mirroring
/// the reference's own Rules step 3 refinement.
#[terminating]
def type_check_named_call (f : Term) (fields : List StructLitField) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError (Option TypedTerm) :=
    match f {
        Term.var _idx dbg =>
            match dbg {
                DebugName.named id =>
                    let bare_name : Identifier := match id { Identifier.id s => Identifier.id (last_dotted_segment s) } in
                    let con_mp : ModulePath := ModulePath.mp (List.cons bare_name List.empty) in
                    match scope_find_inductive_by_constructor con_mp scope {
                        Option.some ind =>
                            match find_constructor_in_inductive ind con_mp {
                                Option.none => ok Option.none,
                                Option.some ctor =>
                                    match ctor {
                                        InductConstructor.mk con_name params _ =>
                                            match named_call_validate_fields params fields {
                                                err e => err e,
                                                ok _ =>
                                                    let args : List (Option Term) := struct_lit_build_args params fields in
                                                    match check_con_args_against_params args params scope local_types locals {
                                                        err e => err e,
                                                        ok elab_args =>
                                                            let mk_name : Identifier := struct_lit_con_name con_name in
                                                            let c : Con := Con.mk mk_name (inductive_module_path ind) (List.length params) elab_args in
                                                            let result_typ : Term := Term.var sentinel (DebugName.named (inductive_bare_name ind)) in
                                                            ok (Option.some (mk_typed (Term.con c) result_typ)),
                                                    }
                                            }
                                    }
                            },
                        // Phase 6: `id` isn't a known constructor -- try an
                        // ordinary def's own declared params instead
                        // (`ScopeData.def_params`, populated by
                        // `build_scope_def`). `scope_resolve_name` (not
                        // the bare-single-segment `con_mp` lookup above)
                        // since an ordinary def's own registered NAME can
                        // be qualified, and `scope_resolve_name` already
                        // handles `open`/`use`/alias resolution the same
                        // way any other free-variable reference does.
                        Option.none =>
                            let nref : NameRef := NameRef.nid id in
                            match scope_resolve_name nref scope locals {
                                err _ => ok Option.none,
                                ok sd =>
                                    match sd {
                                        mk resolved_name _ _ _ =>
                                            match scope_find_def_params resolved_name scope {
                                                Option.none => ok Option.none,
                                                Option.some params =>
                                                    type_check_named_call_def_target f params fields expected_type scope local_types locals,
                                            }
                                    }
                            },
                    },
                DebugName.unnamed => ok Option.none,
            },
        _ => ok Option.none,
    }

/// Def-target branch of `type_check_named_call` (Phase 6). Builds `args`
/// in `params`' declared order (name+type pairs recovered from the def's
/// own `Term.lam` chain by `def_params_of_term`, `lang/scope.mo`), checks
/// each against its own declared type, then folds them into a plain
/// curried `Term.app` chain against `f` -- mirroring the reference
/// compiler's own def-target branch (`try_desugar_named_call`,
/// `core_check.rs`): no per-field type-CORRELATION machinery is needed
/// beyond `type_check` itself, since an ordinary curried application's
/// own per-argument checking already does the right thing at each layer.
def type_check_named_call_def_target (f : Term) (params : List (Pair Identifier Term)) (fields : List StructLitField) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError (Option TypedTerm) :=
    match named_call_def_check_unknown_fields params fields {
        err e => err e,
        ok _ =>
            match named_call_def_pair_args params fields {
                err e => err e,
                ok arg_pairs =>
                    match named_call_def_check_args arg_pairs scope local_types locals {
                        err e => err e,
                        ok _ =>
                            let app_term : Term := named_call_def_fold_app f arg_pairs in
                            ok (Option.some (mk_typed app_term expected_type)),
                    }
            }
    }

/// Every literal field name must be among `params`' own declared names --
/// mirrors `named_call_check_unknown_fields`, just over `List (Pair
/// Identifier Term)` instead of `List Param` (a def's own recovered
/// params carry no full `Param`, only name+type -- see `ScopeData.
/// def_params`'s own doc comment).
#[terminating]
def named_call_def_check_unknown_fields (params : List (Pair Identifier Term)) (fields : List StructLitField) : Result TypeError Bool :=
    match fields {
        List.empty => ok true,
        List.cons f rest =>
            match f {
                StructLitField.mk fname _ =>
                    if def_param_pair_exists params fname
                    then named_call_def_check_unknown_fields params rest
                    else err (TypeError.custom (String.concat "named call: unknown field `" (String.concat (show_identifier fname) "`")))
            }
    }

#[terminating]
def def_param_pair_exists (params : List (Pair Identifier Term)) (name : Identifier) : Bool :=
    match params {
        List.empty => false,
        List.cons p rest =>
            match p {
                Pair.pair pname _ =>
                    if id_eq pname name then true else def_param_pair_exists rest name
            }
    }

/// Builds `(value, declared_type)` pairs in `params`' own declared order
/// -- every param must be covered by a literal field (no default
/// mechanism exists for an ordinary `lang/` def's own params, matching
/// this plan's own `lang/` Non-Goal).
#[terminating]
def named_call_def_pair_args (params : List (Pair Identifier Term)) (fields : List StructLitField) : Result TypeError (List (Pair Term Term)) :=
    match params {
        List.empty => ok List.empty,
        List.cons p rest =>
            match p {
                Pair.pair pname ptyp =>
                    match struct_lit_find_field fields pname {
                        Option.none => err (TypeError.custom (String.concat "named call: missing required field `" (String.concat (show_identifier pname) "`"))),
                        Option.some value =>
                            match named_call_def_pair_args rest fields {
                                err e => err e,
                                ok rest_args => ok (List.cons (Pair.pair value ptyp) rest_args),
                            }
                    }
            }
    }

#[terminating]
def named_call_def_check_args (args : List (Pair Term Term)) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError Bool :=
    match args {
        List.empty => ok true,
        List.cons a rest =>
            match a {
                Pair.pair value ptyp =>
                    match type_check value ptyp scope local_types locals {
                        ok _ => named_call_def_check_args rest scope local_types locals,
                        err e => err e,
                    }
            }
    }

#[terminating]
def named_call_def_fold_app (f : Term) (args : List (Pair Term Term)) : Term :=
    match args {
        List.empty => f,
        List.cons a rest =>
            match a {
                Pair.pair value _ => named_call_def_fold_app (Term.app f value) rest,
            }
    }

/// Type check a struct-update expression (`{ base with field := value,
/// ... }`) by DESUGARING it into a real `Term.con` — mirrors the Rust
/// reference's own `desugar_struct_literals`'s `CoreLit::StructUpdate`
/// arm (`core/src/core_check.rs`): read `base`'s own inferred type to
/// find its registered struct fields, then for each declared field
/// (in the struct's own declaration order) either use the update's own
/// override value if present, or PROJECT it straight out of `base` via
/// a single-case `match` (`struct_update_project_field` below) — the
/// same field-access technique the reference uses (there, an inlined
/// `Match`; here, `Literal.match_`).
///
/// This used to leave a bare `Term.lit (Literal.struct_update base
/// fields)` in place unconditionally — a term `lang/codegen/emit.mo`'s
/// `compile_lit_ir` has no case for at all, so ANY struct-update
/// expression reaching codegen crashed with a non-exhaustive-match
/// error (confirmed: `#[partial]`, only `num`/`flt`/`str`/`if_`/
/// `match_` are handled). Plain struct LITERALS never hit this same
/// crash because `type_check_struct_lit` above already desugars them
/// into `Term.con` — this brings struct UPDATES to the same, already
/// codegen-proven representation instead of teaching codegen a second,
/// parallel way to build a constructor value.
///
/// Falls back to leaving the un-desugared `Literal.struct_update` in
/// place (unchanged from before, so still a crash if actually reached)
/// only when `base`'s type genuinely can't be resolved to a registered
/// struct — matching the reference's own documented fallback for that
/// case (`core_check.rs`'s own comment: "Falls back to leaving a
/// `StructUpdate` literal in place... if `base`'s type can't be
/// determined").
def type_check_struct_update (base : Term) (fields : List StructLitField) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match type_check base Term.hole scope local_types locals {
        err e => err e,
        ok base_tt =>
            let base_term : Term := tt_term base_tt in
            let base_typ : Term := tt_typ base_tt in
            match type_head_name base_typ {
                Option.none => struct_update_fallback base_term fields base_typ,
                Option.some sname =>
                    let typ_mp : ModulePath := ModulePath.mp (List.cons sname List.empty) in
                    match scope_find_inductive typ_mp scope {
                        err _ => struct_update_fallback base_term fields base_typ,
                        ok ind =>
                            match ind {
                                Inductive.mk _ _ _ ctors _ _ =>
                                    match ctors {
                                        List.empty => struct_update_fallback base_term fields base_typ,
                                        List.cons ctor _ =>
                                            match ctor {
                                                InductConstructor.mk con_name params _ =>
                                                    let n : I64 := List.length params in
                                                    let names : List Identifier := struct_param_names params in
                                                    let args : List (Option Term) :=
                                                        struct_update_build_args params fields base_term con_name names n 0 in
                                                    // Each override's value against the struct's own
                                                    // DECLARED field type (`params`), not the blind
                                                    // `Term.hole` pure-infer check this used to run
                                                    // BEFORE the struct was even resolved -- `{ p with
                                                    // x := 5 }` where `p.x : String` now actually
                                                    // rejects the mismatch, mirroring
                                                    // `type_check_struct_lit`'s own `check_con_args_
                                                    // against_params` reuse for ordinary struct
                                                    // literals (`args` already has the same `List
                                                    // (Option Term)`-in-declared-order shape that
                                                    // helper expects).
                                                    match check_con_args_against_params args params scope local_types locals {
                                                        err e => err e,
                                                        ok elab_args =>
                                                            let mk_name : Identifier := struct_lit_con_name con_name in
                                                            let c : Con := Con.mk mk_name typ_mp n elab_args in
                                                            ok (mk_typed (Term.con c) base_typ),
                                                    },
                                            }
                                    }
                            },
                    },
            }
    }

/// Un-resolvable-struct-type fallback: same term this function used to
/// build unconditionally before this fix. Still a crash if it ever
/// actually reaches codegen, but that was already true before this fix
/// and only happens when `base`'s type can't be determined at all
/// (matches the reference's own documented behavior for that case).
def struct_update_fallback (base : Term) (fields : List StructLitField) (base_typ : Term) : Result TypeError TypedTerm :=
    ok (mk_typed (Term.lit (Literal.struct_update base fields)) base_typ)

/// Bare field names of `params`, in declared order — used both as the
/// projection `match`'s own bound-arg names and to walk the struct's
/// declared field order when building `struct_update_build_args`.
#[terminating]
def struct_param_names (params : List Param) : List Identifier :=
    match params {
        List.empty => List.empty,
        List.cons p rest =>
            match p { Param.mk pname _ _ _ _ => List.cons pname (struct_param_names rest) }
    }

/// One arg per declared field, in order: the update's own override
/// value if `fields` has one for that field name, otherwise a
/// `struct_update_project_field` term that reads the unchanged value
/// straight out of `base`.
#[terminating]
def struct_update_build_args (params : List Param) (fields : List StructLitField) (base : Term) (con_name : ModulePath) (all_names : List Identifier) (total : I64) (idx : I64) : List (Option Term) :=
    match params {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Param.mk pname _ _ _ _ =>
                    let value : Term :=
                        match struct_lit_find_field fields pname {
                            Option.some override_term => override_term,
                            Option.none => struct_update_project_field base con_name all_names total idx pname,
                        } in
                    List.cons (Option.some value) (struct_update_build_args rest fields base con_name all_names total (I64.add idx 1))
            }
    }

/// Build a single-case projection `match base { mk f1 f2 ... => f_idx }`
/// term for a struct-update field that ISN'T being overridden — reads
/// the unchanged value straight out of `base` via pattern match, the
/// same technique the Rust reference's own struct-update desugaring
/// uses (`core_check.rs`'s `desugar_struct_literals`, the `StructUpdate`
/// arm, `CoreTerm::Bound((n - 1 - idx) as u32)`). `idx` is 0-based from
/// the FRONT of the struct's declared field order; the de Bruijn index
/// of that same field once all `total` fields are bound as this match
/// arm's own args is `total - 1 - idx` (last-declared = innermost =
/// index 0, this codebase's standard convention — see e.g.
/// `lang/scope.mo`'s `add_constructors_go`).
def struct_update_project_field (base : Term) (con_name : ModulePath) (all_names : List Identifier) (total : I64) (idx : I64) (pname : Identifier) : Term :=
    let bare_name : Identifier := struct_lit_con_name con_name in
    let db_idx : I64 := I64.sub (I64.sub total 1) idx in
    let no_fp : Option FieldPattern := Option.none in
    let case_ : MatchCase := MatchCase.mc bare_name all_names (Term.var db_idx (DebugName.named pname)) no_fp in
    Term.lit (Literal.match_ base (List.cons case_ List.empty))

/// Individually type-check each present argument with no expected type
/// (`Term.hole` — same "no information available" meaning `type_check`
/// itself already gives `Term.hole` elsewhere) — the fallback for a
/// constructor whose inductive type isn't registered in scope, matching
/// `core_check.rs`'s own documented simplification for this case.
///
/// Returns the ELABORATED args (not just success/failure) -- a
/// constructor/struct-literal/struct-update argument that's (or
/// contains) a dot-access field projection (`x.field`, desugared by
/// `field_access_chain`, `lang/parser.mo`, into a single-entry `Literal.
/// match_`) gets REWRITTEN during type-checking (`type_check_field_
/// pattern_case`'s own `declared_order_binders`, above) into a full,
/// declared-order positional match `bind_match_fields`
/// (`lang/codegen/emit.mo`) actually needs to extract the right field.
/// An earlier version of this function (and `check_con_args_against_
/// params` below) only returned `Bool`, discarding that elaboration --
/// every caller then rebuilt the final `Con`/`Term.con` from the
/// ORIGINAL, un-elaborated `args`, so any embedded dot-access argument
/// silently reverted to its single-entry, un-reordered form by the time
/// codegen saw it, and `bind_match_fields`'s positional extraction read
/// field 0 of the wrong object no matter which field was actually named
/// -- confirmed live via a real self-compiled binary's own SIGSEGV
/// (`lang/scope.mo`'s `scope_data_add_instance`, `{ sd with instances :=
/// scope_add_to_instances sd.instances cname ins }`: `sd.instances`
/// -- field index 2 of `ScopeData` -- compiled to read field 0 instead,
/// handing `scope_add_to_instances` an unrelated `HashMap` to recurse
/// into as if it were a `List ScopeInstance`) and independently via a
/// minimal repro (`{ sd with f0 := sd.f1 }` on a 2-field struct reading
/// back the WRONG, pre-update value). Invisible for the overwhelming
/// majority of arguments (plain literals, calls, bare var refs) since
/// their elaborated and un-elaborated forms are identical -- only a
/// dot-access argument's shape actually changes.
#[terminating]
def check_con_args_untyped (args : List (Option Term)) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError (List (Option Term)) :=
    match args {
        List.empty => ok List.empty,
        List.cons a rest =>
            match a {
                Option.none =>
                    match check_con_args_untyped rest scope local_types locals {
                        err e => err e,
                        ok rest_elab => ok (List.cons Option.none rest_elab),
                    },
                Option.some term =>
                    match type_check term Term.hole scope local_types locals {
                        err e => err e,
                        ok tt =>
                            match check_con_args_untyped rest scope local_types locals {
                                err e => err e,
                                ok rest_elab => ok (List.cons (Option.some (tt_term tt)) rest_elab),
                            },
                    }
            }
    }

/// Zip each present argument against the constructor's own declared
/// params, positionally, checking each present arg against its param's
/// literal declared type. If `args` somehow outlasts `params` (shouldn't
/// happen once `type_check_con`'s own arity check has already run, but
/// stay defensive rather than silently skipping the overflow), the
/// remaining args fall back to `check_con_args_untyped`. Returns the
/// ELABORATED args -- see `check_con_args_untyped`'s own doc comment
/// just above for why.
#[terminating]
def check_con_args_against_params (args : List (Option Term)) (params : List Param) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError (List (Option Term)) :=
    match args {
        List.empty => ok List.empty,
        List.cons a rest =>
            match params {
                List.empty => check_con_args_untyped args scope local_types locals,
                List.cons p prest =>
                    match a {
                        Option.none =>
                            match check_con_args_against_params rest prest scope local_types locals {
                                err e => err e,
                                ok rest_elab => ok (List.cons Option.none rest_elab),
                            },
                        Option.some term =>
                            match p {
                                Param.mk _ ptyp _ _ _ =>
                                    match type_check term ptyp scope local_types locals {
                                        err e => err e,
                                        ok tt =>
                                            match check_con_args_against_params rest prest scope local_types locals {
                                                err e => err e,
                                                ok rest_elab => ok (List.cons (Option.some (tt_term tt)) rest_elab),
                                            },
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

// --- Tests for type_check_named_call (Phase 5 of
// plans/implementations/named-field-construction.md) ---
//
// Reuses `point_scope` (above) unchanged for the multi-field case.
// `box_scope` is NOT reusable here for a single-field case: its own
// constructor is registered under a 2-segment path (`box_ctor_full_
// path = mp [Box, box]`, needed by `type_check_con`'s OWN tests, which
// resolve via `scope_find_inductive(typ_name)` + the constructor's FULL
// path within it) -- but `type_check_named_call` resolves `f` the SAME
// way `type_check_free_var_con` does: `scope_find_inductive_by_
// constructor`, a flat scope-wide search keyed on a SINGLE-segment
// bare name only (`last_dotted_segment` always collapses `f`'s own
// identifier down to one segment before searching) -- matching real
// scope registration's own "constructors registered under their bare
// name only" convention (`add_constructors_go`, `lang/scope.mo`, per
// `type_check_free_var_con`'s own doc comment). A dedicated single-
// field `Solo { n }` fixture, registered bare (mirroring `point_scope`'s
// own "mk" path), is what this actually needs.

def point_mk_var : Term := Term.var sentinel (DebugName.named (Identifier.id "mk"))

def solo_type_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Solo") List.empty)

def solo_mk_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "mk") List.empty)

def solo_n_param : Param := Param.mk (Identifier.id "n") (Term.type_ 2) Multiplicity.many Option.none List.empty

def solo_constructor : InductConstructor := InductConstructor.mk solo_mk_path (List.cons solo_n_param List.empty) Term.hole

def solo_inductive : Inductive := Inductive.mk solo_type_path List.empty Term.hole (List.cons solo_constructor List.empty) List.empty Visibility.package_private

def solo_scope : Scope := {
    module_id := solo_type_path,
    scope := scope_data_add_inductive scope_data_empty solo_inductive,
    parent := Option.none,
}

def solo_mk_var : Term := Term.var sentinel (DebugName.named (Identifier.id "mk"))

#[test]
def test_type_check_named_call_multi_field_reordered : Bool :=
    // Fields given in the OPPOSITE order from `point_params`' own
    // declaration (y then x) -- order-independence is the whole point.
    let fy : StructLitField := StructLitField.mk (Identifier.id "y") (Term.type_ 1) in
    let fx : StructLitField := StructLitField.mk (Identifier.id "x") (Term.type_ 1) in
    let fields : List StructLitField := List.cons fy (List.cons fx List.empty) in
    match type_check_named_call point_mk_var fields Term.hole point_scope empty_local_types empty_locals {
        ok result => match result {
            Option.some _ => true,
            Option.none => false,
        },
        err _ => false,
    }

#[test]
def test_type_check_named_call_single_field_constructor : Bool :=
    let f1 : StructLitField := StructLitField.mk (Identifier.id "n") (Term.type_ 1) in
    let fields : List StructLitField := List.cons f1 List.empty in
    match type_check_named_call solo_mk_var fields Term.hole solo_scope empty_local_types empty_locals {
        ok result => match result {
            Option.some _ => true,
            Option.none => false,
        },
        err _ => false,
    }

#[test]
def test_type_check_named_call_unknown_field_is_an_error : Bool :=
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.type_ 1) in
    let f2 : StructLitField := StructLitField.mk (Identifier.id "y") (Term.type_ 1) in
    let bad : StructLitField := StructLitField.mk (Identifier.id "z_not_a_field") (Term.type_ 1) in
    let fields : List StructLitField := List.cons f1 (List.cons f2 (List.cons bad List.empty)) in
    match type_check_named_call point_mk_var fields Term.hole point_scope empty_local_types empty_locals {
        err _ => true,
        ok _ => false,
    }

#[test]
def test_type_check_named_call_missing_field_is_an_error : Bool :=
    // No default mechanism exists for `lang/` constructors of any kind --
    // omitting `y` must always be an error here, UNLIKE `type_check_
    // struct_lit`'s own leniency (`test_type_check_struct_lit_missing_
    // field_ok`, above) -- a positive, deliberate strictness difference
    // (see `named_call_validate_fields`'s own doc comment), not a gap.
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.type_ 1) in
    let fields : List StructLitField := List.cons f1 List.empty in
    match type_check_named_call point_mk_var fields Term.hole point_scope empty_local_types empty_locals {
        err _ => true,
        ok _ => false,
    }

#[test]
def test_type_check_named_call_not_a_constructor_returns_none : Bool :=
    // `f` doesn't resolve to a known constructor at all -- the SHAPE
    // doesn't apply, so callers must fall back to the ORIGINAL error
    // (Phase 6 will try an ordinary def's own params here instead, once
    // that resolution infrastructure lands).
    let unknown_var : Term := Term.var sentinel (DebugName.named (Identifier.id "not_a_real_name")) in
    let fields : List StructLitField := List.empty in
    match type_check_named_call unknown_var fields Term.hole point_scope empty_local_types empty_locals {
        ok result => match result {
            Option.none => true,
            Option.some _ => false,
        },
        err _ => false,
    }

#[test]
def test_type_check_app_resolves_named_call_end_to_end : Bool :=
    // Full `type_check_app` dispatch (not `type_check_named_call`
    // directly): `mk { y := .., x := .. }` parses as `App(Var(mk),
    // StructLit)` -- confirms the fallback actually wires up inside
    // `type_check_app` itself, not just as a standalone function.
    let fy : StructLitField := StructLitField.mk (Identifier.id "y") (Term.type_ 1) in
    let fx : StructLitField := StructLitField.mk (Identifier.id "x") (Term.type_ 1) in
    let fields : List StructLitField := List.cons fy (List.cons fx List.empty) in
    let arg : Term := Term.lit (Literal.struct_lit fields Option.none) in
    match type_check_app point_mk_var arg Term.hole point_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

// --- Tests for type_check_named_call's def-target branch (Phase 6 of
// plans/implementations/named-field-construction.md) ---
//
// Hand-built `Def` (name "scale", two params "factor"/"p" of type
// `Term.type_ 2`, body `Term.type_ 1` -- same sort-level convention
// `box_scope`/`point_scope` use above, and for the same reason: only a
// `Term.type_ N` argument actually exercises `type_check_sort_full`'s
// own comparison against a declared param type, unlike a literal/
// free-var argument which would trivially "pass" any type), registered
// via the REAL `build_scope_def` (not a hand-assembled `ScopeData`
// literal) so this exercises the actual `def_params_of_term`/`scope_
// data_add_def_params` registration path, not just its consumer.

def scale_def_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "scale") List.empty)

def scale_def_body : Term :=
    Term.lam (DebugName.named (Identifier.id "factor")) (Term.type_ 2)
        (Term.lam (DebugName.named (Identifier.id "p")) (Term.type_ 2) (Term.type_ 1))

def scale_def : Def := {
    name := scale_def_name,
    typ := Term.hole,
    term := scale_def_body,
    constraints := List.empty,
    attrs := List.empty,
    vis := Visibility.package_private,
}

def scale_scope : Scope := {
    module_id := scale_def_name,
    scope := build_scope_def scale_def scale_def_name scope_data_empty,
    parent := Option.none,
}

def scale_var : Term := Term.var sentinel (DebugName.named (Identifier.id "scale"))

#[test]
def test_type_check_named_call_def_target_reordered : Bool :=
    // Fields given in the OPPOSITE order from `scale_def_body`'s own
    // declaration (p then factor).
    let fp : StructLitField := StructLitField.mk (Identifier.id "p") (Term.type_ 1) in
    let ff : StructLitField := StructLitField.mk (Identifier.id "factor") (Term.type_ 1) in
    let fields : List StructLitField := List.cons fp (List.cons ff List.empty) in
    match type_check_named_call scale_var fields Term.hole scale_scope empty_local_types empty_locals {
        ok result => match result {
            Option.some _ => true,
            Option.none => false,
        },
        err _ => false,
    }

#[test]
def test_type_check_named_call_def_target_wrong_field_type_rejected : Bool :=
    // `factor`'s declared param type is `Term.type_ 2` -- a sort at level
    // 5 is not a valid inhabitant, same reasoning as the constructor-
    // target `wrong_arg_type`/`wrong_field_type` tests above.
    let fp : StructLitField := StructLitField.mk (Identifier.id "p") (Term.type_ 1) in
    let ff : StructLitField := StructLitField.mk (Identifier.id "factor") (Term.type_ 5) in
    let fields : List StructLitField := List.cons fp (List.cons ff List.empty) in
    match type_check_named_call scale_var fields Term.hole scale_scope empty_local_types empty_locals {
        err _ => true,
        ok _ => false,
    }

#[test]
def test_type_check_named_call_def_target_unknown_field_is_an_error : Bool :=
    let fp : StructLitField := StructLitField.mk (Identifier.id "p") (Term.type_ 1) in
    let ff : StructLitField := StructLitField.mk (Identifier.id "factor") (Term.type_ 1) in
    let bad : StructLitField := StructLitField.mk (Identifier.id "not_a_param") (Term.type_ 1) in
    let fields : List StructLitField := List.cons fp (List.cons ff (List.cons bad List.empty)) in
    match type_check_named_call scale_var fields Term.hole scale_scope empty_local_types empty_locals {
        err _ => true,
        ok _ => false,
    }

#[test]
def test_type_check_named_call_def_target_missing_field_is_an_error : Bool :=
    // No default mechanism exists for ordinary `lang/` def params --
    // omitting `p` must always be an error.
    let ff : StructLitField := StructLitField.mk (Identifier.id "factor") (Term.type_ 1) in
    let fields : List StructLitField := List.cons ff List.empty in
    match type_check_named_call scale_var fields Term.hole scale_scope empty_local_types empty_locals {
        err _ => true,
        ok _ => false,
    }

#[test]
def test_type_check_app_resolves_def_target_named_call_end_to_end : Bool :=
    // Full `type_check_app` dispatch: `scale { p := .., factor := .. }`
    // parses as `App(Var(scale), StructLit)`.
    let fp : StructLitField := StructLitField.mk (Identifier.id "p") (Term.type_ 1) in
    let ff : StructLitField := StructLitField.mk (Identifier.id "factor") (Term.type_ 1) in
    let fields : List StructLitField := List.cons fp (List.cons ff List.empty) in
    let arg : Term := Term.lit (Literal.struct_lit fields Option.none) in
    match type_check_app scale_var arg Term.hole scale_scope empty_local_types empty_locals {
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

/// Regression test for the struct-update codegen crash fix: the checked
/// term must be a real `Term.con` (the SAME representation
/// `type_check_struct_lit` already produces, which
/// `lang/codegen/emit.mo`'s `compile_db_term_ir`/`compile_con_ir`
/// already compile correctly) — NOT a bare `Term.lit
/// (Literal.struct_update ...)`, which `compile_lit_ir` has no real
/// codegen for. Before this fix, `type_check_struct_update` ALWAYS
/// produced the latter.
#[test]
def test_type_check_struct_update_desugars_to_con : Bool :=
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.type_ 1) in
    let fields : List StructLitField := List.cons f1 List.empty in
    match type_check_struct_update point_var fields Term.hole point_scope point_local_types empty_locals {
        ok tt => match tt_term tt {
            Term.con _ => true,
            _ => false,
        },
        err _ => false,
    }

/// The overridden field (`x`) becomes the override's own value
/// (arg 0, matching `point_params`' declared order `x`, `y`); the
/// UNCHANGED field (`y`) becomes a projection `match` reading it back
/// out of `base`, not the override value and not left blank.
#[test]
def test_type_check_struct_update_unchanged_field_is_projection : Bool :=
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.type_ 1) in
    let fields : List StructLitField := List.cons f1 List.empty in
    match type_check_struct_update point_var fields Term.hole point_scope point_local_types empty_locals {
        ok tt => match tt_term tt {
            Term.con c => match c {
                Con.mk _name _typ_name _arity args => match args {
                    List.cons x_arg rest => match rest {
                        List.cons y_arg _ =>
                            is_type_arg x_arg && is_match_arg y_arg,
                        List.empty => false,
                    },
                    List.empty => false,
                },
            },
            _ => false,
        },
        err _ => false,
    }

#[partial]
def is_type_arg (arg : Option Term) : Bool :=
    match arg {
        Option.some t => match t { Term.type_ _ => true, _ => false },
        Option.none => false,
    }

#[partial]
def is_match_arg (arg : Option Term) : Bool :=
    match arg {
        Option.some t => match t {
            Term.lit l => match l { Literal.match_ _ _ => true, _ => false },
            _ => false,
        },
        Option.none => false,
    }

/// The un-resolvable-struct-type fallback (`base`'s type isn't a
/// registered struct at all) still produces the pre-fix representation
/// — matches the Rust reference's own documented fallback behavior for
/// this case. `Term.hole` is not a struct type, so `type_head_name`
/// returns `Option.none` and the fallback path is taken.
#[test]
def test_type_check_struct_update_unresolvable_base_falls_back : Bool :=
    let unresolvable_base : Term := Term.hole in
    let fields : List StructLitField := List.empty in
    match type_check_struct_update unresolvable_base fields Term.hole point_scope empty_local_types empty_locals {
        ok tt => match tt_term tt {
            Term.lit l => match l { Literal.struct_update _ _ => true, _ => false },
            _ => false,
        },
        err _ => false,
    }

// --- Regression: struct-update overrides are checked against the
// struct's own DECLARED field type, not blindly accepted (`Term.hole`)
// ---
//
// `point_scope`'s own `x`/`y` fields are typed `Term.type_ 2` (a bare
// sort, deliberately permissive so the OTHER struct-update tests above
// can freely use `Term.type_ 1` as a stand-in override value) -- too
// permissive to demonstrate a real rejection via cumulativity. This
// fixture instead gives `Wrap`'s one field a CONCRETE, non-sort type
// (`Point`, reusing `point_type_ref`), so an override of a different,
// structurally-unrelated shape (`Term.type_ 1`) has somewhere real to
// conflict with.

def wrap_type_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Wrap") List.empty)

def wrap_mk_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "mk") List.empty)

def wrap_v_param : Param := Param.mk (Identifier.id "v") point_type_ref Multiplicity.many Option.none List.empty

def wrap_constructor : InductConstructor := InductConstructor.mk wrap_mk_path (List.cons wrap_v_param List.empty) Term.hole

def wrap_inductive : Inductive := Inductive.mk wrap_type_path List.empty Term.hole (List.cons wrap_constructor List.empty) List.empty Visibility.package_private

def wrap_scope : Scope := {
    module_id := wrap_type_path,
    scope := scope_data_add_inductive scope_data_empty wrap_inductive,
    parent := Option.none,
}

def wrap_local_types : List Term := List.cons (Term.var sentinel (DebugName.named (Identifier.id "Wrap"))) empty_local_types

def wrap_var : Term := Term.var 0 (DebugName.named (Identifier.id "w"))

#[test]
def test_type_check_struct_update_rejects_mismatched_field_type : Bool :=
    // `v : Point`, overridden with `Term.type_ 1` (a bare sort) --
    // structurally unrelated to a concrete `Point` reference, so this
    // must be REJECTED. Before this fix (`struct_update_check_fields`
    // checking every override against `Term.hole`, i.e. "anything
    // goes"), this incorrectly returned `ok`.
    let f1 : StructLitField := StructLitField.mk (Identifier.id "v") (Term.type_ 1) in
    let fields : List StructLitField := List.cons f1 List.empty in
    match type_check_struct_update wrap_var fields Term.hole wrap_scope wrap_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }
// The "a genuine override still succeeds" positive path is already
// covered by `test_type_check_struct_update_ok`/`_result_type_is_base_
// type`/`_desugars_to_con` above (all against `point_scope`, whose
// fields are deliberately abstract-sort-typed) -- no separate positive
// companion needed here.
