use std::map {HashMap.to_list}
use lang::types {
  Binder, Class, Con, Cubical, CubicalPrim, DebugName, Def, Elim, FieldPattern,
  FieldPatternEntry, Identifier, InductConstructor, Inductive, Instance, Literal,
  LocalScope, LocalVar, Location, MatchCase, ModulePath, NamePath, NameRef,
  Native, NumSuffix, Param, Scope, ScopeClassDef, ScopeData, ScopeDef,
  ScopeError, Similar, SortLevel, StructLitField, Term, TypeConstraint,
  TypeError, binder_anon, binder_is_explicit, binder_is_level, binder_name,
  binder_named,
  concrete, cub_glue, cub_glue_elim, cub_glue_intro, cub_hcomp, cub_i0, cub_i1,
  cub_interval, cub_is_one,
  cub_pathp, cubical_arity,
  cubical_prim_eq, cubical_prim_name, field_access_chain,
  id_eq, id_member, level_lt, level_of_type, list_rev_loop, list_reverse, many,
  max, package_private, sentinel, show_identifier, show_name_path,
  sort_level_of, sort_n, succ, term_peel,
  cub, cub_transp,
}
use lang::scope {
  ClassMethodRef, DictBinding, bind_term_vars, build_dict_field_projection_checked,
  build_scope_def, bare_map_lookup, carrier_bindings, class_method_declared_type, class_method_ref,
  class_default_carrier, class_name_eq,
  class_method_var_names, class_param_names, dict_binding_class_of, final_result_type,
  method_carrier_hint, method_sig_carrier,
  dict_hint_marker_terms, dict_hint_name, dict_param_name, emitted_dict_constraints,
  find_constructor_in_inductive, find_matching_instance,
  flatten_call_spine, identifier_tail, inductive_has_constructor, instance_module_prefix,
  instance_wildcard_names, instance_head_is_concrete, list_append, mangle_instance_dict_name,
  mangle_instance_method_name, mangled_to_identifier, param_names,
  rebuild_call,
  resolve_dict_args, scope_data_add_inductive, scope_data_classes, scope_data_constrained_def_classes,
  scope_data_empty, scope_find_all_inductives_by_constructor, scope_find_class,
  scope_find_class_def_by_name, scope_find_class_def_for_ref, scope_find_def_dict_constraints,
  scope_find_def_params, scope_find_def_return_type,
  scope_find_def_sig, scope_find_inductive, scope_find_inductive_by_constructor,
  scope_find_instance_by_name, scope_find_local, scope_globals,
  scope_all_instances_in, scope_instance_candidates_in, scope_push_local,
  scope_find_cubical_prim, scope_resolve_name, strip_all_leading_binders,
  strip_dict_hint_args,
  type_mentions_any, validate_dict_hints,
}
use lib::typecheck::name_subst {name_subst_term}
use lib::typecheck::subst {beta_reduce, term_abstract_var, term_permute, term_subst, term_shift}
use lib::typecheck::levels {solve_levels, subst_levels_term}
use lib::typecheck::traverse {term_children}
use lib::typecheck::cubical {
  PathParts, endpoint_of, path_parts_of, peels_to_bare_interval,
}
use lib::typecheck::unify {unify, unify_structural}
use lib::typecheck::whnf {whnf}
use std::list {List.length}

/// A type-checked term paired with its type.
pub struct TypedTerm {
    term : Term,
    typ : Term,
}

/// A type-checked match case with inferred body type.
pub struct CheckedCase {
    case_ : MatchCase,
    body_typ_ : Term,
}

/// Accumulator for processing match cases: the unified body
/// type and the checked cases in reverse order.
pub struct CaseAcc {
    body_typ : Term,
    cases : List MatchCase,
}

/// Empty local scope (no local bindings).
pub def empty_locals : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

/// Empty list of local types (no de Bruijn bindings).
pub def empty_local_types : List Term := List.empty

/// Is this reference qualified by a CLASS name (`Sub.sub`)? See the guard
/// in `try_type_check_con_call`.
#[partial]
def qualified_by_class (id : Identifier) (scope : Scope) : Bool :=
    match id {
        Identifier.id s =>
            match dotted_qualifier s {
                Option.some q =>
                    match scope_find_class (NamePath.mk (List.cons (Identifier.id q) List.empty)) scope {
                        Option.some _ => true,
                        Option.none => false,
                    },
                Option.none => false,
            },
    }

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
///
/// Several arms return their OWN type without comparing it against
/// `expected_type` (`type_check_lit`, `type_check_con`, and
/// `type_check_bound_var` behind `type_check_var`). That is deliberate
/// here and gated one level up instead: `lang/module.mo`'s
/// `body_signature_diagnostics` compares a def BODY's checked type against
/// the def's declared one, which is where the difference is a bug rather
/// than a placeholder.
pub def type_check (term : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match term {
        Term.lit value => type_check_lit value expected_type scope local_types locals,
        Term.var idx dbg => type_check_var idx dbg expected_type scope local_types locals,
        Term.lam dbg t body => type_check_lam dbg t body expected_type scope local_types locals,
        Term.app f a => type_check_app f a expected_type scope local_types locals,
        // One arm for all three binder flavours. `b` is handed through
        // unchanged: it carries the NAME (`wrap_forall`/`wrap_level_forall`
        // put the variable's own name there) and the INFO that tells a
        // quantified type variable, a universe level and an ordinary arrow
        // apart -- rebuilding it as `binder_anon`, which is what the old
        // `type_check_pi` did, would erase both.
        Term.pi b arg ret => type_check_pi b arg ret scope local_types locals,
        Term.con c => type_check_con c expected_type scope local_types locals,
        Term.ntv ntv => type_check_ntv ntv expected_type scope local_types locals,
        // The sole sort form -- `Prop`/`Type`/`Sort n` all lower to it. The
        // term is handed through as it is; `type_check_sort_full` computes the
        // universe one level up from the level it carries.
        Term.sort level => type_check_sort_full (Term.sort level) level expected_type,
        // Struct literals in ctor-arg position must be bound to an
        // annotated local first (AGENTS.md): a bare `{ ... }` reaching
        // `ok`'s argument gets no expected type (constructor sigs are
        // `Term.hole`), so the named-call path can't resolve its fields.
        Term.hole => ok (mk_typed expected_type expected_type),
        Term.quote_ _ => err (TypeError.custom "unresolved quote reached the type checker (macro expansion should have resolved it first)"),
        Term.var_macro _ _ => err (TypeError.custom "unresolved macro-template variable reached the type checker (macro expansion should have resolved it first)"),
        // PRESERVING. `elaborate_decl_with_scope` (`lang/module.mo`) writes
        // the checker's rewritten `TypedTerm.term` back into the `Def`, and
        // elaboration runs on the compile path -- so dropping the wrapper
        // here would erase every source position before codegen ever sees
        // one, and the whole feature would silently do nothing.
        Term.ctx loc inner => type_check_located loc inner expected_type scope local_types locals,
        // Stage 1 of the cubical fragment carries only the interval and its
        // De Morgan operations, whose rules are small enough to state here;
        // `PathP`/`transp`/`hcomp` get their own module
        // (`lang/typecheck/cubical.mo`) when they land.
        Term.cubical c => type_check_cubical c expected_type scope local_types locals,
        // `core-term-simplification.md` R4: the explicit-motive typing
        // rule for dependent elimination. See `type_check_elim` below.
        Term.elim e => type_check_elim e expected_type scope local_types locals,
    }

/// Re-wrap a located term's checked result. Split out because the rewrap
/// needs the `ok`/`err` split and nested patterns are unsupported.
#[partial]
def type_check_located (loc : Location) (inner : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match type_check inner expected_type scope local_types locals {
        ok tt => ok (mk_typed (Term.ctx loc tt.term) tt.typ),
        err e => err e,
    }

/// Is `t` one of the sort terms (`Prop`/`Type`/`Sort n`)?
def is_sort_typ (t : Term) : Bool :=
    match t {
        Term.sort _ => true,
        _ => false,
    }

/// Is `t` a function type?
def is_pi_typ (t : Term) : Bool :=
    match t {
        Term.pi _ _ _ => true,
        _ => false,
    }

/// Does `t` contain a `Term.hole` anywhere?
#[terminating]
def term_has_hole (t : Term) : Bool :=
    match t {
        Term.hole => true,
        _ => any_term_has_hole (term_children t),
    }

#[terminating]
def any_term_has_hole (ts : List Term) : Bool :=
    match ts {
        List.empty => false,
        List.cons x rest => if term_has_hole x then true else any_term_has_hole rest,
    }

/// Does `t` mention a BOUND variable -- a de Bruijn index, not the free-var
/// sentinel? A DEPENDENT parameter type does: `fiber (A : Type) (B : Type)
/// (f : A -> B) (b : B)` records `b`'s domain still referencing the `A`/
/// `B` binders, so it cannot be compared with a closed argument type until
/// the earlier arguments are substituted into it -- which this checker does
/// not do. `call_arg_type_error` declines on such a parameter rather than
/// reporting the raw index as a mismatch.
#[terminating]
def term_has_bound_var (t : Term) : Bool :=
    match t {
        Term.var idx _ => Bool.not (I64.beq idx sentinel),
        _ => any_term_has_bound_var (term_children t),
    }

#[terminating]
def any_term_has_bound_var (ts : List Term) : Bool :=
    match ts {
        List.empty => false,
        List.cons x rest =>
            if term_has_bound_var x then true else any_term_has_bound_var rest,
    }

/// Does `t` mention a type variable that is still UNINSTANTIATED -- a name
/// `locals` skolemized, or a name nothing in `scope` binds?
#[terminating]
def mentions_uninstantiated_typevar (t : Term) (scope : Scope) (locals : LocalScope) : Bool :=
    match t {
        Term.var idx dbg =>
            if I64.beq idx sentinel then
                match dbg {
                    DebugName.named nm =>
                        match scope_find_local nm locals {
                            Option.some _ => true,
                            Option.none =>
                                match scope_resolve_name (NameRef.nid nm) scope empty_locals {
                                    Result.ok _ => false,
                                    // Nothing binds it: it is the callee's
                                    // own type variable, which
                                    // instantiating a cross-def reference
                                    // did not substitute away.
                                    Result.err _ => true,
                                },
                        },
                    _ => false,
                }
            else false,
        _ => any_mentions_uninstantiated (term_children t) scope locals,
    }

#[terminating]
def any_mentions_uninstantiated (ts : List Term) (scope : Scope) (locals : LocalScope) : Bool :=
    match ts {
        List.empty => false,
        List.cons x rest =>
            if mentions_uninstantiated_typevar x scope locals
            then true
            else any_mentions_uninstantiated rest scope locals,
    }

/// The ONE definition of "is this body's type the type it was expected to
/// have", shared by def bodies (`lang/module.mo`'s
/// `body_signature_diagnostics`, i.e. every top-level def) and lambda
/// bodies (`type_check_lam_explicit`, i.e. the parameterised half).
///
/// It exists because `type_check` returns its own idea of a term's type,
/// and for several arms that idea is either not compared against
/// `expected_type` at all (`type_check_lit`, `type_check_con`,
/// `type_check_bound_var`) or is a placeholder. `unify` accepts a
/// `Term.hole` on either side, so the comparison only ever bites where
/// both sides carry real information -- which is exactly where silence was
/// a bug: `def p : I64 := "hello"` used to check cleanly.
///
/// Four guards, each forced by a corpus measurement rather than written
/// defensively:
///   - a body containing a `Term.hole` is not a finished body:
///     `def p1 : T -> T := apply (fn x => x) _` infers `T`, because
///     `type_check_app` does not carry the callee's return type through a
///     hole ARGUMENT (`lang/src/module.mo`'s own
///     `test_hole_in_infer_position_accepts_named_callee*` pins);
///   - either side mentioning a skolemized or unbound type variable is not
///     a fair comparison: a generic def's body infers an INSTANTIATED type
///     (`def empty_arities : HashMap String I64 := str_map_empty` infers
///     `HashMap String V`; `lang.scope`'s `npath_map_empty` infers
///     `HashMap K V`);
///   - two SORTS are compared by CUMULATIVITY (`type_check_sort_full`),
///     which `unify` does not implement --
///     `let _f : (Sort 1 -> Sort 2) := fn x => x` (`init/src/tests.mo`'s
///     `test_pi_universe`) is legitimate and `unify (Sort 2) (Sort 1)`
///     rejects it.
pub def body_type_error (body : Term) (inferred : Term) (expected : Term)
    (scope : Scope) (locals : LocalScope) : Option TypeError :=
    if term_has_hole body then Option.none
    else if is_sort_typ expected then Option.none
    else if mentions_uninstantiated_typevar expected scope locals then Option.none
    else if mentions_uninstantiated_typevar inferred scope locals then Option.none
    else match unify expected inferred scope locals {
        Result.ok _ => Option.none,
        Result.err e => Option.some e,
    }

/// Build a TypedTerm from term and type.
def mk_typed (a : Term) (b : Term) : TypedTerm :=
    { term := a, typ := b }

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
///
/// The fallback to the WHOLE `t` applies only when `t` is not a Pi at all
/// -- a bare expected type with no application to answer, the
/// `Default.default` shape above. It used to be reachable THROUGH a Pi
/// chain too (an uninformative domain recursed into the enclosing
/// expected type), and that is unsound: for `K.k [42]` as a def's whole
/// body, the Pi domain is the argument's own type and the enclosing
/// expected type is the DEF'S DECLARED RETURN TYPE, which has nothing to
/// do with the carrier. MEASURED (probe, 2026-09-19): `def t1 : Bool :=
/// K.k [42]` with instances at `Bool`/`String`/`List A` dispatched to
/// `K_Bool_k`, and `def t6 : String := K.k [true]` to `K_String_k` --
/// the return type winning over the argument, in the one position where
/// the enclosing expectation is a return type rather than an argument's
/// unknown. Everywhere else (the call nested as an `if` condition, an
/// `==` operand, a let-bound value) the domain IS informative and the
/// argument's own `List I64` wins, which is what makes this a
/// position- dependent bug and not a missing feature.
///
/// So an uninformative domain now searches only the REST OF THE PI CHAIN
/// (`carrier_from_pi_chain`) and reports `Option.none` at the end of it
/// rather than reaching the enclosing type. `Option.none` is the honest
/// answer -- the checker then falls back to the class method's abstract
/// signature (`type_check_free_var`'s own `err _ =>` arm, which
/// documented itself as covering exactly the shapes this checker can't
/// recover) and leaves the call for `lang.scope`'s syntactic pass, which
/// derives the carrier from the call's ARGUMENTS -- the source that was
/// right all along here.
def carrier_from_expected_type (t : Term) : Option Term :=
    match t {
        // The guard is R2b's, and it is NOT the same question
        // `is_uninformative_carrier` below asks. Before the fold this
        // function had an arm for `pi` and none for `forall`, so a
        // quantifier-headed expectation fell to `_ => Option.some t` --
        // the whole quantifier handed back as if it were a carrier.
        // Folding makes `forall` a `pi`, which without the guard would
        // silently route it through the arrow rule instead (skip the
        // sort domain, recurse into the body). That looks like a
        // fix -- `is_uninformative_carrier`'s own rule says a sort
        // domain says nothing -- but it is a SEMANTIC change to
        // instance resolution and R2b is a representation change.
        // `binder_is_explicit` keeps the old answer bit for bit; the
        // widening is its own step, with its own pins.
        Term.pi b arg_typ ret_typ =>
            if binder_is_explicit b
            then
                if is_uninformative_carrier arg_typ then carrier_from_pi_chain ret_typ else Option.some arg_typ
            else Option.some t,
        Term.hole => Option.none,
        _ => Option.some t,
    }

/// The rest of a Pi chain after an uninformative domain: the next
/// informative domain, if any. Sibling of `carrier_from_expected_type`,
/// which cannot recurse into itself for this -- that recursion is the
/// enclosing-expected-type leak its own doc comment describes. Never
/// returns the chain's final codomain: a codomain is a RETURN type, and
/// a carrier is never a return type.
#[partial]
def carrier_from_pi_chain (t : Term) : Option Term :=
    match t {
        // Same guard, same reason as `carrier_from_expected_type` above:
        // this one's old answer for a quantifier-headed chain was the
        // catch-all `Option.none`, i.e. STOP. The fold would otherwise
        // skip the quantifier's sort domain and walk into its body.
        Term.pi b arg_typ ret_typ =>
            if binder_is_explicit b
            then
                if is_uninformative_carrier arg_typ then carrier_from_pi_chain ret_typ else Option.some arg_typ
            else Option.none,
        _ => Option.none,
    }

/// `is_hole` alone isn't enough: a sort is equally uninformative -- a Pi
/// domain holding one says no more about the value than a hole does.
/// Treating it the same as `Term.hole` here -- skip to the next Pi domain
/// rather than accepting it as a carrier -- mirrors why the OLD syntactic
/// pass (`lang.scope`'s `infer_carrier_type`) never trusted a
/// type-checker-reported literal type either, matching on the literal
/// VALUE directly instead (`literal_carrier_type`).
///
/// MEASURED, and the reason this arm exists: `"/" ++ rest`'s OUTER `++`
/// carrier came back as literally `Type` instead of `String`, because
/// `"/"`'s sibling operand `rest`'s own Pi-domain position was checked
/// first and happened to be a nested `++` chain whose OWN innermost
/// literal polluted an intermediate Pi arg with a sort. `type_check_lit`
/// now answers the literal's own REAL type (`String`/`I64`/...), so that
/// route is closed; the arm stays because a sort reaching a Pi domain by
/// any route is still uninformative.
def is_uninformative_carrier (t : Term) : Bool :=
    match t {
        Term.hole => true,
        // A sort is a universe placeholder too.
        Term.sort _ => true,
        // So is the interval: an `I -> A` binder is a dimension binder
        // (Stage 1 step 4), and a dimension says nothing about `A`'s
        // value -- leaving this arm out makes `carrier_from_pi_chain`
        // report `I` as the instance carrier of every `I -> A`, and
        // instance resolution silently picks wrong. Arity 0 is part of
        // the test: a cubical term with arguments is a dimension
        // EXPRESSION, not the interval itself, and stays a candidate.
        Term.cubical c =>
            match c {
                { prim := p, args := as } =>
                    cubical_prim_eq p CubicalPrim.interval && List.is_empty as,
            },
        _ => false,
    }

/// Is there already a bound local dict param for `cls_name` in scope
/// (Phase 3's own `__dict_ClassName` naming, `lang.scope`'s
/// `dict_param_name`)? D5 forwarding -- inside a still-generic
/// constrained def's own body, the concrete instance isn't known yet,
/// only a dict VALUE already bound as a parameter. The exact-name lookup
/// keys off `cls_name`'s OWN spelling, which is the class's qualified
/// registration name since item 5.1 -- while the param itself was NAMED
/// from the constraint's bare source spelling (constraints are never
/// rewritten), so retry by comparing each `__dict_*` local's own
/// recovered class via `class_name_eq` -- the same tolerance every other
/// D5 site (`lookup_dict_binding`, the syntactic pass's own tier) already
/// uses; without the retry, D5 silently misses and D4 emits a direct
/// call to the generic instance's method def with no dict argument.
def local_dict_for_class (cls_name : NamePath) (locals : LocalScope) : Option Identifier :=
    match scope_find_local (Identifier.id (dict_param_name cls_name)) locals {
        Option.some lv => Option.some lv.name,
        Option.none => local_dict_by_class_eq cls_name (local_vars_flat locals),
    }

#[partial]
def local_dict_by_class_eq (cls_name : NamePath) (vars : List LocalVar) : Option Identifier :=
    match vars {
        List.empty => Option.none,
        List.cons lv rest =>
            match dict_binding_class_of lv.name {
                Option.some bcls => if class_name_eq bcls cls_name then Option.some lv.name else local_dict_by_class_eq cls_name rest,
                Option.none => local_dict_by_class_eq cls_name rest,
            },
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
/// Strip `n` leading `Term.pi` binders (skipping over any quantified or
/// level binder met at each step -- they don't correspond to an applied
/// value argument), returning the final codomain. `binder_is_explicit` is
/// the test; the guard is load-bearing rather than tidiness, because
/// counting a former `forall` as a value binder would report a def's type
/// one argument short. Needed because
/// `resolve_class_method_d4`'s reported type must be the RESOLVED
/// concrete def's own real signature (peeled by however many dict args
/// got pre-applied), not `expected_type` verbatim -- `expected_type`
/// itself can be partially uninformative -- a bare sort rather than a real
/// type can sit in one of its Pi domains (see `is_uninformative_carrier`'s
/// own doc comment for the measurement) -- and reusing it verbatim as this
/// call's reported type would cascade that uninformativeness upward into
/// the NEXT enclosing `type_check_
/// app`'s own carrier derivation -- confirmed as the actual root cause
/// of a real repro (the self-hosted test driver's own synthesized
/// summary line) via direct debugging.
#[partial]
def strip_n_pis (typ : Term) (n : I64) : Term :=
    if I64.lt n 1 then typ
    else
        match typ {
            Term.pi b _dom ret =>
                if binder_is_explicit b then strip_n_pis ret (n - 1) else strip_n_pis ret n,
            _ => typ,
        }

/// Drop the `n` leading hole-typed dictionary Pis of a promoted method's signature.
#[partial]
def strip_dict_pis (typ : Term) (n : I64) : Term :=
    if I64.lt n 1 then typ
    else
        match typ {
            Term.pi _b dom ret =>
                match dom {
                    Term.hole => strip_dict_pis ret (n - 1),
                    _ => typ,
                },
            _ => typ,
        }

/// How many leading dict Pis Phase 3 prepended
/// (`add_constraint_dict_params`, `lang.scope`): one per qualifying
/// constraint, in constraint-list order. Phase 3 builds them with
/// `binder_anon`, so the binder must be UNNAMED too -- a real parameter
/// annotated `_` is also a hole-domain Pi, and stripping it would shift
/// every remaining argument.
#[partial]
def count_dict_pis (typ : Term) : I64 :=
    match typ {
        Term.pi b dom ret =>
            match dom {
                Term.hole =>
                    match binder_name b {
                        DebugName.unnamed => 1 + count_dict_pis ret,
                        DebugName.named _ => 0,
                    },
                _ => 0,
            },
        _ => 0,
    }

/// The constraints that became dictionary PARAMETERS. Registered at
/// scope-build time with the shared predicate over the same body and
/// list Phase 3 read, so this list and the signature's leading hole Pis
/// agree by construction (the Layer-1 ABI rule) -- and no call site
/// re-walks the callee's body.
def qualifying_def_constraints (name : NamePath) (scope : Scope) : List TypeConstraint :=
    match scope_find_def_dict_constraints name scope {
        Option.some cs => cs,
        Option.none => List.empty,
    }

#[partial]
def constraint_var_list (cs : List TypeConstraint) : List Identifier :=
    match cs {
        List.empty => List.empty,
        List.cons c rest =>
            match c {
                TypeConstraint.mk _ vars => List.append vars (constraint_var_list rest),
            },
    }

#[partial]
def binding_of (bindings : List (Pair Identifier Term)) (v : Identifier) : Option Term :=
    match bindings {
        List.empty => Option.none,
        List.cons b rest =>
            match b {
                Pair.pair id t => if id_eq id v then Option.some t else binding_of rest v,
            },
    }

/// Is this binding value usable as evidence? A placeholder is not, and
/// neither is a bare variable that does not name a type in scope -- the
/// constraint's own `M` solved to itself (`M := M` from an abstract
/// argument) is the question, not an answer, and a wildcard-headed
/// bridge instance matches it anyway.
#[partial]
def informative_value (t : Term) (scope : Scope) : Bool :=
    if is_uninformative_carrier t then false
    else
        match term_peel t {
            Term.var _ dbg =>
                match dbg {
                    DebugName.named id => is_scope_type_name id scope,
                    DebugName.unnamed => false,
                },
            _ => true,
        }

/// Every constraint variable bound to something informative. Until this
/// holds, no carrier is offered at all, so a hole can never be matched
/// by a wildcard-headed bridge instance.
def constraint_vars_informative (cs : List TypeConstraint) (bindings : List (Pair Identifier Term)) (scope : Scope) : Bool :=
    match cs {
        List.empty => true,
        List.cons c rest =>
            match c {
                TypeConstraint.mk _ vars => vars_informative_go vars bindings scope && constraint_vars_informative rest bindings scope,
            },
    }

#[partial]
def vars_informative_go (vars : List Identifier) (bindings : List (Pair Identifier Term)) (scope : Scope) : Bool :=
    match vars {
        List.empty => true,
        List.cons v rest =>
            (match binding_of bindings v {
                Option.some t => informative_value t scope,
                Option.none => false,
            }) && vars_informative_go rest bindings scope,
    }

#[partial]
def first_bound_value_go (vars : List Identifier) (bindings : List (Pair Identifier Term)) : Option Term :=
    match vars {
        List.empty => Option.none,
        List.cons v rest =>
            match binding_of bindings v {
                Option.some t => Option.some t,
                Option.none => first_bound_value_go rest bindings,
            },
    }

/// The first bound constraint value, as the fallback carrier when the
/// expectation yielded none: `constraint_vars_informative` already
/// proved every variable bound, so this never has to invent one.
#[partial]
def first_bound_constraint_value (constraints : List TypeConstraint) (bindings : List (Pair Identifier Term)) : Option Term :=
    first_bound_value_go (constraint_var_list constraints) bindings

#[partial]
def informative_carrier_of (t : Term) : Option Term :=
    match carrier_from_expected_type t {
        Option.some c => if is_uninformative_carrier c then Option.none else Option.some c,
        Option.none => Option.none,
    }

/// Every constraint is either already forwarded from this scope's own
/// dictionary environment or has every variable bound to an informative
/// value. The second half is Item 2's invariant: a hole carrier must
/// never reach `resolve_dict_arg`, where a wildcard-headed bridge
/// instance matches it and `arg_is_dict` makes the wrong committed
/// dictionary final. The first half is sound for the SAME reason -- a
/// constraint answered by a local binding (`local_dict_for_class`, the
/// D5 tier `resolve_dict_arg` reads before any carrier) does no carrier
/// matching at all -- and its absence suppressed a forward this checker
/// can make: a `through [Bind M] := step m` body solves `M` to itself,
/// so the whole-call guard refused even though `__dict_Bind` is bound
/// right there.
def constraints_resolvable (cs : List TypeConstraint) (bindings : List (Pair Identifier Term)) (scope : Scope) (locals : LocalScope) : Bool :=
    match cs {
        List.empty => true,
        List.cons c rest =>
            constraint_resolvable c bindings scope locals && constraints_resolvable rest bindings scope locals,
    }

#[partial]
def constraint_resolvable (c : TypeConstraint) (bindings : List (Pair Identifier Term)) (scope : Scope) (locals : LocalScope) : Bool :=
    match c {
        TypeConstraint.mk cls vars =>
            match local_dict_for_class cls locals {
                Option.some _ => true,
                Option.none => vars_informative_go vars bindings scope,
            },
    }

/// The dictionary arguments a constrained call resolves to, or
/// `Option.none` when this checker has no sound answer: no bindings, no
/// informative carrier, or any dictionary unresolved. Shared by the
/// applied-call and bare-reference paths so they cannot diverge about
/// when a dictionary is inserted.
def dict_args_for_constraints (constraints : List TypeConstraint) (bindings : List (Pair Identifier Term)) (carrier : Option Term) (scope : Scope) (locals : LocalScope) : Option (List Term) :=
    if Bool.not (constraints_resolvable constraints bindings scope locals) then Option.none
    else
        let fallback : Option Term :=
            match carrier {
                Option.some c => Option.some c,
                Option.none => first_bound_constraint_value constraints bindings,
            } in
        match fallback {
            Option.some c =>
                resolve_dict_args (scope_data_classes (scope_globals scope)) (scope_all_instances_in scope) (dict_env_from_locals locals) List.empty bindings c List.empty constraints,
            Option.none => Option.none,
        }

/// Insert the dict argument(s) an ordinary constrained def CALL needs
/// into its elaborated spine -- the checker-side counterpart of
/// `resolve_ordinary_constrained_call`. Bindings are what
/// `try_type_check_def_call` already solved (arguments, then the
/// expected-type return direction); the expected type is also the
/// fallback carrier, reifying the syntactic pass's annotated-binding
/// expectation channel at every call site. Returned unchanged on any
/// miss -- the syntactic pass still runs afterwards. Hints are skipped
/// here (the syntactic pass owns hint resolution; a marker-first spine
/// would defeat its `arg_is_dict` guard).
def reify_ordinary_dict_args (name : NamePath) (k : I64) (hints : List String) (markers : List Term) (arg_bindings : List (Pair Identifier Term)) (ret_bindings : List (Pair Identifier Term)) (expected_type : Term) (scope : Scope) (locals : LocalScope) (head : Term) (elab_args : List Term) : Term :=
    let plain : Term := rebuild_call head (List.append markers elab_args) in
    if Bool.or (I64.lt k 1) (I64.gt (List.length hints) 0) then plain
    else
        let constraints : List TypeConstraint := qualifying_def_constraints name scope in
        if Bool.not (I64.beq (List.length constraints) k) then plain
        else
            match dict_args_for_constraints constraints (List.append arg_bindings ret_bindings) (informative_carrier_of expected_type) scope locals {
                Option.some dict_args =>
                    if I64.beq (List.length dict_args) k
                    then rebuild_call head (List.append markers (List.append dict_args elab_args))
                    else plain,
                Option.none => plain,
            }

/// A BARE reference to an ordinary constrained def (`op` in
/// `let x : Id I64 := op in ...`) needs the same dict argument a call
/// site gets; with no value arguments, the expected type is the only
/// evidence. Unchanged wherever it can't resolve.
def reify_bare_constrained_ref (name : NamePath) (declared : Term) (expected_type : Term) (scope : Scope) (locals : LocalScope) (dbg : DebugName) : Result TypeError TypedTerm :=
    let plain : Result TypeError TypedTerm := ok (mk_typed (Term.var sentinel dbg) declared) in
    let k : I64 := count_dict_pis declared in
    let constraints : List TypeConstraint := qualifying_def_constraints name scope in
    if Bool.or (I64.lt k 1) (Bool.not (I64.beq (List.length constraints) k)) then plain
    else
        let dict_free : Term := strip_dict_pis declared k in
        let bindings : List (Pair Identifier Term) :=
            bind_term_vars (constraint_var_list constraints) (strip_all_leading_binders dict_free) (term_peel expected_type) List.empty in
        // The binding above is the WHOLE expected type; the fallback
        // carrier must be the same term, not its Pi domain.
        let carrier : Option Term :=
            match informative_carrier_of expected_type {
                Option.some _ => Option.some (term_peel expected_type),
                Option.none => Option.none,
            } in
        match dict_args_for_constraints constraints bindings carrier scope locals {
            Option.some dict_args =>
                if I64.beq (List.length dict_args) k
                then ok (mk_typed (rebuild_call (Term.var sentinel dbg) dict_args) dict_free)
                else plain,
            Option.none => plain,
        }

/// Does this call's own nested constraint dictionary reference the
/// ENCLOSING instance's own dictionary -- `BEq (Option A)`'s element
/// constraint resolving back to `__Dict_BEq_Option_A`?
///
/// That is never a valid resolution. The constraint is on the instance's
/// own type VARIABLE (`[BEq A]`), and matching it against the WHOLE
/// carrier re-finds the very instance being expanded, so the promoted
/// method would be handed its own dictionary in its element slot and
/// recurse without bound. MEASURED (2026-09-21, A8): `some 1 ==
/// (List.get 0 [1, 2, 3])` resolved to `BEq_Option_A_beq(
/// __Dict_BEq_Option_A(), some 1, List.get 0 [1, 2, 3])` -- the driver
/// then died at the first element read (`driver exited -1`, and
/// `init/src/tests.mo`'s whole file with it).
///
/// `lang.scope`'s own `resolve_dict_arg` does not have this problem: its
/// candidate list carries the call's own argument carriers
/// (`extra_carriers`), so it can fall through to the concrete element
/// carrier this pure-infer-mode checker never sees. It is also the pass
/// that runs last, so erring here is how this call reaches it: see
/// `term_is_self_dict`'s own doc comment for why `err` is the right
/// answer rather than a diagnostic.
def dict_args_contain_self (self_dict : Identifier) (dict_args : List Term) : Bool :=
    match dict_args {
        List.empty => false,
        List.cons a rest =>
            term_is_self_dict self_dict a || dict_args_contain_self self_dict rest,
    }

/// Is `t` a reference to `self_dict`? The dictionary arguments
/// `resolve_dict_arg` builds are `Term.var (0 - 1) (DebugName.named
/// <mangled dict name>)` sentinels (`lang/scope.mo`), never a real local
/// at any depth, so a by-name comparison is exact.
///
/// The caller's answer to a `true` here is `err`, deliberately: it lands
/// in `type_check_free_var`'s own `err _ =>` fallback, which leaves the
/// call as an unresolved class-method reference -- and `lang.scope`'s
/// syntactic `resolve_class_calls_decls` pass, which every codegen path
/// still runs afterwards, resolves exactly this call correctly from the
/// arguments' own carriers. A dictionary this checker cannot pin down is
/// not a user-facing error: reporting one would trade a correct
/// resolution for a spurious diagnostic, and this is the one shape where
/// the checker's own answer is provably wrong rather than merely
/// uninformed.
def term_is_self_dict (self_dict : Identifier) (t : Term) : Bool :=
    match term_peel t {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => Similar.similar id self_dict,
                DebugName.unnamed => false,
            },
        _ => false,
    }

def resolve_class_method_d4
    (insname : Identifier) (ins_cls_name : NamePath) (method_name : Identifier)
    (ins_constraints : List TypeConstraint) (ins_args : List Term) (carrier : Term)
    (bindings : List (Pair Identifier Term))
    (expected_type : Term) (scope : Scope) (locals : LocalScope)
    : Result TypeError TypedTerm :=
    let mangled := mangle_instance_method_name insname ins_cls_name ins_args method_name in
    let mangled_id := mangled_to_identifier mangled in
    match scope_resolve_name (NameRef.nid mangled_id) scope locals {
        err _ => err (TypeError.custom "instance is missing its promoted method"),
        ok resolved_sd =>
            // The resolved def's REAL declared signature, out of the
            // `def_sigs` side-table -- NOT `ScopeDef.sig`, which
            // `build_scope_def` (`lang/scope.mo`) sets to `Term.hole`
            // unconditionally for every def (a sentinel its own doc
            // comment calls load-bearing for dozens of call sites, so it
            // cannot simply be filled in there). Reading `.sig` made this
            // function's own doc comment -- "the resolved concrete def's
            // own real signature" -- false, and typed EVERY class-method
            // call in the checker as a hole.
            let real_sig : Term :=
                match scope_find_def_sig resolved_sd.name scope {
                    Option.some s => s,
                    Option.none => resolved_sd.sig,
                } in
            // A registry signature keeps its implicit type variables FREE
            // (`List A` for `FromListLiteral_List_empty`), and an
            // unsolved one is not a usable type: it travels upward still
            // abstract and meets the declared return in
            // `type_check_cases` as "type mismatch: expected (List A),
            // found (List U8)". The ambient `expected_type` at the
            // callee's own position is what says what those variables
            // are -- solve the signature against it exactly as
            // `def_call_continue` solves a def's declared parameters
            // against its arguments. Uninformative (a hole, or a shape
            // mismatch) records nothing, leaving the signature untouched
            // rather than rewriting it wrongly.
            //
            // MEASURED: this pair (`inst_sig` here + the `pi_ret`
            // substitution below) changes NO corpus file's verdict on
            // its own -- `init std examples lang cli llvm runtime motes
            // slow_tests bench` reports the same 15 errors in the same 7
            // files with and without it. It is the precondition, not the
            // trigger: `FromListLiteral.cons` has to RESOLVE to this
            // promoted def before any signature is read at all, and the
            // carrier that makes it resolve (`List (List A)` from
            // `List.flatten`) needs the applied-head match in
            // `term_matches_carrier` (`lang/scope.mo`) that P6 owns.
            // Verified together: P5 + that match closes
            // `std/src/sha256.mo` at both check and runner level.
            // The leading dictionary parameters (hole-typed) are not arguments of the
            // call being solved, and would shift every later domain by one.
            let solved : List (Pair Identifier Term) :=
                solve_typevars scope (strip_dict_pis real_sig (List.length ins_constraints)) expected_type List.empty in
            let inst_sig : Term := subst_typevars_term real_sig solved in
            let mangled_ref : Term := Term.var sentinel (DebugName.named mangled_id) in
            match ins_constraints {
                List.empty => ok (mk_typed mangled_ref inst_sig),
                List.cons _ _ =>
                    let classes := scope_data_classes (scope_globals scope) in
                    // All classes' instances: a constraint of ANOTHER class (`[Add A] HAdd A A A`) is resolved here too.
                    let instances := scope_all_instances_in scope in
                    let dict_env := dict_env_from_locals locals in
                    // `List.empty` -- extending this call site with the same
                    // args-derived `extra_carriers` fallback `lang.scope`'s
                    // codegen pass now has (`resolve_dict_arg`'s own doc
                    // comment) is out of scope here: this checker-level path
                    // doesn't hard-fail on a miss anyway (see
                    // `resolve_class_method`'s own `err _ =>` fallback to the
                    // method's abstract signature, `type_check_free_var`).
                    //
                    // But this call site is NOT merely advisory, and the
                    // older form of this comment claimed otherwise: a call
                    // that succeeds HERE is rewritten and is never handed to
                    // `lang.scope`'s pass again, so a wrong answer is FINAL.
                    // That is exactly how A8 got into the emitted driver --
                    // this function resolved `[BEq A]` against the whole
                    // generic carrier and produced `__Dict_BEq_Option_A` for
                    // `BEq (Option A)`'s own element slot. Hence the
                    // self-reference refusal below, which defers instead of
                    // answering.
                    //
                    // The BINDINGS are not optional, though: what the
                    // matched instance's own head binds for the call site
                    // (`List I64` against `(List A)` binds `A := I64`) is
                    // the only thing that makes a nested constraint
                    // resolvable. Without it `[Show A]` resolves against
                    // the WHOLE carrier `List I64`, which matches the very
                    // instance being expanded -- `Show (List A)` -- so the
                    // dict argument came back as the instance's own
                    // dictionary, a self-reference applied to each element.
                    // MEASURED (probe, 2026-09-19): every class call with a
                    // list-literal argument that this checker resolved
                    // (an `if` condition, an `==` operand, a let-bound
                    // value -- anywhere the enclosing expectation is not a
                    // return type) compiled to
                    // `<Cls>_List_A_m(__Dict_<Cls>_List_A, ...)` -- the
                    // same `lang.scope` codegen pass's own
                    // `carrier_bindings`/`resolve_dict_arg` pair fixes on
                    // its side. The bindings themselves are computed at
                    // the CALL SITE (`resolve_class_method`), which is
                    // where the matched `Instance` is in hand.
                    // A constraint on a variable the instance head does not bind
                    // (`[BOrd K]` on `Map BTreeMap`) is read off the call's own
                    // signature: `K` is whatever the expected type puts there.
                    let call_bindings : List (Pair Identifier Term) := List.append bindings solved in
                    match resolve_dict_args classes instances dict_env List.empty call_bindings carrier List.empty ins_constraints {
                        Option.none => err (TypeError.custom "cannot resolve inner instance dictionary"),
                        Option.some dict_args =>
                            // Refuse the self-match -- see
                            // `dict_args_contain_self`'s own doc comment.
                            // The candidate order here (`bindings` first,
                            // then the whole `carrier`) is right for a
                            // constraint on a DIFFERENT type variable than
                            // the instance's own (`Map`'s `[BOrd K]`) and
                            // wrong for the common same-variable case
                            // whenever the carrier is still generic:
                            // `List.get 0 [1, 2, 3]` leaves the carrier at
                            // `Option A`, so `[BEq A]`'s own `A` binds to
                            // that unresolved `A` and the whole-carrier
                            // fallback lands back on `BEq (Option A)` --
                            // the instance being expanded.
                            if dict_args_contain_self (mangled_to_identifier (mangle_instance_dict_name insname ins_cls_name ins_args)) dict_args
                            then err (TypeError.custom "self-referential instance dictionary")
                            else
                                let applied_typ : Term := strip_n_pis inst_sig (List.length dict_args) in
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
                    match dict_forwarding_override class_name cls method_name expected_type scope {
                        // `_checked` sibling, not `build_dict_field_projection`
                        // itself -- this result gets re-typechecked (this
                        // resolution happens while `elaborate_loaded_modules`'
                        // rewritten decls are later re-checked by `check_
                        // module_with_scope`), so it needs the checker's
                        // by-name free-var convention, not codegen's raw
                        // de-Bruijn-index-0 one. See both functions' own doc
                        // comments (`lang/scope.mo`) for the full D5 story.
                        Option.none =>
                            let term := build_dict_field_projection_checked cls dict_id method_name List.empty in
                            ok (mk_typed term expected_type),
                        Option.some carrier =>
                            resolve_class_method_carrier class_name method_name carrier expected_type scope locals,
                    },
                Option.none =>
                    let direct : Result TypeError TypedTerm :=
                        match carrier_from_expected_type expected_type {
                            Option.none => err (TypeError.custom "cannot infer carrier type for class method"),
                            Option.some carrier =>
                                resolve_class_method_carrier class_name method_name carrier expected_type scope locals,
                        } in
                    match direct {
                        ok tt => if mentions_hole expected_type then ok (open_method_vars cls method_name tt) else direct,
                        err _ =>
                            match class_has_single_param cls {
                                false => direct,
                                true =>
                                    resolve_with_carrier_hint class_name cls method_name expected_type scope locals
                                        (method_carrier_hint cls method_name (Option.some (final_result_type expected_type)))
                                        (resolve_with_carrier_hint class_name cls method_name expected_type scope locals
                                            (method_sig_carrier cls method_name expected_type)
                                            (resolve_with_carrier_hint class_name cls method_name expected_type scope locals
                                                (class_default_carrier cls) direct)),
                            },
                    },
            },
    }

/// `hint` as the carrier when it resolves, `otherwise` when it is absent or does not.
def resolve_with_carrier_hint (class_name : NamePath) (cls : Class) (method_name : Identifier) (expected_type : Term) (scope : Scope) (locals : LocalScope) (hint : Option Term) (otherwise : Result TypeError TypedTerm) : Result TypeError TypedTerm :=
    match hint {
        Option.none => otherwise,
        Option.some carrier =>
            match resolve_class_method_carrier class_name method_name carrier expected_type scope locals {
                ok tt => ok (open_method_vars cls method_name tt),
                err _ => otherwise,
            },
    }

/// A call resolved only from its expected RESULT has the method's own type
/// variables (`A` in `pure : A -> M A`) still unsolved; the checker has no metas,
/// so they become holes rather than rigid names no later arm could agree with.
def open_method_vars (cls : Class) (method_name : Identifier) (tt : TypedTerm) : TypedTerm :=
    match class_method_declared_type cls method_name {
        Option.none => tt,
        Option.some sig =>
            TypedTerm.mk tt.term (fill_unsolved_vars (class_method_var_names cls sig) tt.typ),
    }

/// The declared field count of `ind`'s constructor named `name`.
def constructor_arity_of (ind : Inductive) (name : Identifier) : Option I64 :=
    match ind {
        Inductive.mk _ _ _ ctors _ _ => constructor_arity_in ctors name,
    }

#[partial]
def constructor_arity_in (ctors : List InductConstructor) (name : Identifier) : Option I64 :=
    match ctors {
        List.empty => Option.none,
        List.cons c rest =>
            match c {
                InductConstructor.mk cname params _ =>
                    if constructor_name_matches cname name
                    then Option.some (List.length params)
                    else constructor_arity_in rest name,
            },
    }

/// `InductConstructor.name` is a full `NamePath`; a case carries the bare
/// identifier, matched against the path's LAST segment (the same
/// normalisation `constructor_bare_name` performs).
def constructor_name_matches (cname : NamePath) (name : Identifier) : Bool :=
    match cname {
        NamePath.mk segs =>
            match list_last segs {
                Option.some last => id_eq last name,
                Option.none => false,
            },
    }


/// Whether `t` still has a hole: a partial expectation (`IO _`) fixes the
/// carrier but not the method's own variables.
#[partial]
def mentions_hole (t : Term) : Bool :=
    match t {
        Term.hole => true,
        _ => any_mentions_hole (term_children t),
    }

#[partial]
def any_mentions_hole (ts : List Term) : Bool :=
    match ts {
        List.empty => false,
        List.cons x rest => if mentions_hole x then true else any_mentions_hole rest,
    }

/// A heterogeneous class (`HAdd A B C`) has no single carrier to read off a
/// result type, so the result-type fallback applies to one-parameter classes only.
def class_has_single_param (cls : Class) : Bool :=
    match cls {
        Class.mk _ params _ _ _ =>
            match params {
                List.cons _ rest =>
                    match rest {
                        List.empty => true,
                        _ => false,
                    },
                _ => false,
            },
    }

/// D4 (instance-lookup) resolution of a class method call at an already
/// known `carrier`. Factored out of `resolve_class_method` so both of its
/// non-forwarding paths share it verbatim.
def resolve_class_method_carrier (class_name : NamePath) (method_name : Identifier) (carrier : Term) (expected_type : Term) (scope : Scope) (locals : LocalScope) : Result TypeError TypedTerm :=
    let candidates := scope_instance_candidates_in scope class_name in
    match find_matching_instance candidates class_name carrier {
        Option.none => err (TypeError.custom "no matching instance found"),
        Option.some ins =>
            let bindings : List (Pair Identifier Term) :=
                carrier_bindings (instance_wildcard_names ins) ins.args carrier in
            resolve_class_method_d4 ins.name ins.cls method_name (emitted_dict_constraints (scope_data_constrained_def_classes (scope_globals scope)) (scope_data_classes (scope_globals scope)) ins method_name) ins.args carrier bindings expected_type scope locals,
    }

/// The carrier a call INSIDE a dictionary-carrying scope must be resolved
/// against instead of forwarding to the enclosing `__dict_<Cls>`, or
/// `Option.none` when forwarding IS the right answer.
///
/// Forwarding is the norm and the whole point of D5: `instance [BEq A]
/// BEq (List A)`'s body is written at the ELEMENT type, so its own
/// `x == y` is `BEq.beq x y` with `x : A`, and the instance's `__dict_BEq`
/// parameter -- the dictionary for `A`, handed in by whoever called
/// `BEq (List A)` -- is exactly the dictionary that comparison needs.
///
/// It is wrong for the same body's OTHER call, the recursive
/// `BEq.beq x_tail y_tail` (both tails are `List A`, the type the
/// instance is FOR): that one must reach the instance itself
/// (`BEq_List_A_beq __dict_BEq x_tail y_tail`). Forwarding instead hands
/// the ELEMENT dictionary two lists, which dies at the first list cell
/// read as a scalar -- MEASURED as `driver exited -1` on
/// `std/src/sha256_tests.mo` and eight more files, and as a wrong answer
/// (`[1,2,3] == [1,2,3]` is false) in the one place the crash is
/// survivable.
///
/// What tells the two apart is the call's own argument type, and the
/// checker already has it: `type_check_app_ordinary` checks the callee
/// against `Term.pi <argument type> <enclosing expectation>`, so
/// `carrier_from_expected_type` reads it off that domain. A carrier
/// written in the CLASS'S OWN parameter names (the bare `A` whose
/// dictionary the local is) means forwarding; a concrete carrier that
/// MATCHES an instance of this class means the instance wins.
///
/// `Option.none` -- forward -- is the answer for everything these two
/// tests cannot decide (an uninformative domain, a carrier no instance
/// matches), so every call that forwards correctly today forwards exactly
/// as it did.
def dict_forwarding_override (cls_name : NamePath) (cls : Class) (method_name : Identifier) (expected_type : Term) (scope : Scope) : Option Term :=
    match carrier_from_expected_type expected_type {
        Option.none => Option.none,
        Option.some carrier =>
            if carrier_is_class_param cls method_name carrier
            then Option.none
            else match find_matching_instance (scope_instance_candidates_in scope cls_name) cls_name carrier {
                Option.none => Option.none,
                // A VARIABLE-HEADED instance (the prelude's
                // `instance {I} [IndexedMonad M] Monad (M I I)`) matches
                // any carrier whose head is a type variable, and it is
                // never the "the instance wins" answer this branch is
                // for: inside a dict-carrying scope the local
                // `__dict_<Cls>` is the dictionary for the class's own
                // parameter, and diverting to that instance only fails
                // on ITS `[IndexedMonad M]` constraint (measured: every
                // `[Monad M]` def in `init/transformers.mo`, whose
                // `Monad.pure` is checked at the ARGUMENT's type --
                // `R`, `Option B` -- and matched the bridge). A concrete
                // head (`instance [BEq A] BEq (List A)`'s `List A`, the
                // recursive-tail case this branch exists for) still
                // diverts.
                Option.some ins => if instance_head_is_concrete ins then Option.some carrier else Option.none,
            },
    }

/// Is `carrier` written AT the class's own dictionary type -- a bare
/// `Term.var` naming one of the class's own parameters (or of the
/// parameters its method signature applies, `M K V` for `Map`)? An
/// APPLIED carrier is not: `List A` inside `instance [BEq A] BEq (List
/// A)` names a type the instance is for, not the `A` its dictionary is
/// the dictionary of. See `dict_forwarding_override`.
def carrier_is_class_param (cls : Class) (method_name : Identifier) (carrier : Term) : Bool :=
    let names :=
        match class_method_declared_type cls method_name {
            Option.some sig => class_method_var_names cls sig,
            Option.none => class_param_names cls,
        } in
    match term_peel carrier {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => id_member id names,
                DebugName.unnamed => false,
            },
        _ => false,
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
        // A bare sort (a KIND, not a real type) used to be returned here
        // unconditionally regardless of what kind of literal this actually
        // is -- harmless as long as the caller's `expected_type` was always
        // `Term.hole` (`unify` accepts anything against a hole), which was
        // true for every match-arm body reached from an ordinary top-level
        // def until `check_def_with_scope` started passing the def's own
        // real declared type through. Once a real expected type reaches
        // here (e.g. an `I64`-returning def whose body is a match with an
        // `n => 0` arm), `unify` on that sort against `I64` correctly
        // failed with "type mismatch: expected Type, found I64" --
        // confirmed via a minimal repro (`def f (n : Nat) : I64 := match n
        // { zero => 0, succ m => 1 }`). Returning the literal's own REAL
        // type (from its `NumSuffix`, or `String` for a string literal)
        // fixes this at the source rather than special-casing `unify` to
        // treat a sort as a wildcard (which would also weaken genuine
        // Sort/Type-as-value checks elsewhere, e.g. the Sort/Pred tests).
        Literal.str s =>
            ok (mk_typed (Term.lit value) (named_type_ref "String")),
        // Same shape as the `String` arm above -- a char literal's own
        // REAL type, so `def c : Char := 'M'` checks. `Char` has no
        // operations at all (AGENTS.md item 29), so nothing consumes the
        // result yet; this only stops the literal from being untypeable.
        Literal.char c =>
            ok (mk_typed (Term.lit value) (named_type_ref "Char")),
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
///
/// The condition's expected type is `Bool`, spelled the way the parser
/// spells a type reference. It used to be `Term.sort (concrete 1)` under
/// the name `bool_typ` -- the KIND `Type`, not the type `Bool`. Most
/// condition shapes never consult an expectation, so that went unnoticed
/// until one did: a field access desugars to a `match`, and
/// `type_check_cases` unifies the arm's real type against it, so
/// `if f.done then ...` failed with "expected Bool, found Type" (and,
/// before that unification existed, elaborated to a field read at index 0
/// -- the segfault in `plans/implementations/2026-10-04-struct-field-
/// access-as-if-cond-segfaults-nonzero-index.md`).
def type_check_if (one : Term) (two : Term) (three : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    let bool_typ : Term := named_type_ref "Bool" in
    match type_check one bool_typ scope local_types locals {
        ok cond_tt =>
            let cond_term : Term := cond_tt.term in
            match type_check two expected_type scope local_types locals {
                ok then_tt =>
                    let then_term : Term := then_tt.term in
                    let then_typ : Term := then_tt.typ in
                    match type_check three then_typ scope local_types locals {
                        ok els_tt =>
                            let els_term : Term := els_tt.term in
                            let els_typ : Term := els_tt.typ in
                            // The else arm is CHECKED against the then type,
                            // but the checker's arms mostly ignore an
                            // expectation (`type_check_lit`, `type_check_con`,
                            // the free/bound var arms), so the checked type was
                            // discarded and `if b then IO.pure 0 else
                            // IO.pure (Result.ok Unit.unit)` checked cleanly --
                            // one arm yielding an `I64` box and the other a
                            // constructor, with nothing saying so. The match
                            // arm result is the one boundary that already
                            // enforced this; `if` now does too.
                            match body_type_error three els_typ then_typ scope locals {
                                Option.some e => err e,
                                Option.none =>
                            let lit_val : Literal := Literal.if_ cond_term then_term els_term in
                            ok (mk_typed (Term.lit lit_val) then_typ),
                            },
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
            let sc_term : Term := sc_tt.term in
            let sc_typ : Term := sc_tt.typ in
            match validate_match_constructors cases sc_term sc_typ scope {
                err e => err e,
                ok maybe_ind => type_check_cases cases sc_term sc_typ maybe_ind expected_type scope local_types locals,
            },
        err e => err e,
    }

// ─── R4: the `Elim` typing rule (core-term-simplification.md) ───────────
//
// Dependent elimination with an explicit motive. Per the R4 reconnaissance
// recorded in the plan doc, every primitive this rule needs already
// exists: `scope_find_inductive` resolves `e.inductive`; `rebuild_call`/
// `free_var_ref` rebuild the scrutinee's expected type from `e.inductive`
// applied to `e.params`, checked by ordinary `unify` (mirrors
// `validate_match_constructors`'s own scrutinee handling);
// `substitute_inductive_type_params` (R3b) instantiates each
// constructor's field types; the `type_check_pathp_go`/
// `type_check_hcomp_go` pattern (infer motive, peel to `Term.pi`, require
// the codomain to satisfy `sort_level_of`) checks the motive is a
// function into a sort; and `Term.app motive scrutinee` -- an
// UNREDUCED application, the same device `extract_path_app` already uses
// for `p i`'s type -- is both a minor's expected result type (applied to
// that constructor) and the elim's own overall type, with no new
// substitution primitive needed. No motive DERIVATION happens here (that
// is R4b, not yet scoped) -- this rule only checks a motive it is given.

/// A free reference to a resolved name, by its full qualified path --
/// `named_type_ref` generalized from a bare `String` to a `NamePath`,
/// matching the established idiom at `lang/scope.mo:1923`
/// (`Term.var idx (DebugName.named (Identifier.id (show_name_path
/// target)))`) for turning a resolved name into a term.
def free_var_ref (np : NamePath) : Term :=
    Term.var sentinel (DebugName.named (Identifier.id (show_name_path np)))

// ─── R4b: motive derivation (core-term-simplification.md) ───────────────
//
// `type_check_elim`'s motive is checked, never derived -- it is the
// CALLER's job to build one when a `match`/`if` is elaborated against a
// dependent expected type that mentions the scrutinee (`sigma-types.md`'s
// `Sigma.snd : B (Sigma.fst p) := match p { dpair a b => b }` is the
// motivating case: the expected type `B (Sigma.fst p)` must become the
// motive `fn q => B (Sigma.fst q)` for `type_check_elim_motive` to accept
// a minor whose own inferred type is `B a`, not `B (Sigma.fst p)`
// syntactically). `derive_motive` is that builder: wrap `term_abstract_var`
// (`subst.mo`, this step's own new primitive) in exactly the one `Term.lam`
// `type_check_elim_motive` expects to peel.
//
// NOT wired into `type_check_if`/`type_check_match` -- that would mean
// giving `type_check_match` a real `Term.elim`-producing fallback path,
// which is `R3c`'s job, and R3c's own reconnaissance
// (`core-term-simplification.md`) found that blocked on `emit.mo`/
// `lower_core_ir.mo` gaining real `Term.elim` support first. So a real
// source-level `def Sigma.snd := match p { dpair a b => b }` still cannot
// be *written and compiled* after this step -- what this step delivers is
// the derivation RULE itself, pinned directly against `type_check_elim`
// the same way R4's own dependent-motive pin exercises the CHECKING rule
// without going through real `match` syntax.
//
// Scoped to a scrutinee that is itself an ordinary BOUND VARIABLE
// (`scrutinee_idx`), matching `term_abstract_var`'s own documented scope --
// not an arbitrary compound scrutinee expression, and not an INDEXED
// family's extra index arguments (`Eq A a b`'s `b`, needed for `Eq.rec`/
// `T.rec` -- recorded as a separate, not-yet-scoped follow-on, R4c, since
// it needs `Elim` itself to grow an indices field, a `Term`-shape change
// on the order of R3a, not just a new substitution primitive).
def derive_motive (scrutinee_idx : I64) (scrutinee_typ : Term) (expected_type : Term) : Term :=
    Term.lam binder_anon scrutinee_typ (term_abstract_var scrutinee_idx expected_type)

/// The `Elim` typing rule. Resolves `inductive`, checks the scrutinee
/// against it applied to `params`, then hands off to the motive check.
/// `e` is destructured by NAMED field (not `Elim.mk a b c d e f`
/// positionally, which the style ratchet's `wide_positional_pattern_
/// violation` counter flags, and not `e.scrutinee` by projection, which
/// breaks the termination checker's structural-decrease proof for the
/// call into `type_check` below) -- the same idiom `term_has_struct_
/// lit`'s own `elim` arm (R3a, `lang/codegen/validate.mo`) already uses
/// for exactly this reason.
///
/// `#[terminating]`: the call into `type_check_elim_motive` below carries
/// `ind`/`sc_tt.term`/`sc_tt.typ` alongside `e`, which throws off the
/// automatic positional decrease check once the two calls' arities
/// differ -- the same reason `type_check_cases_accum`'s own accumulator
/// parameters need this. The real decrease is still `scrutinee`/`motive`/
/// each minor being genuine subterms of `e`, as the call into plain
/// `type_check` just above proves on its own (same arity, decrease found
/// automatically, no annotation needed there).
#[terminating]
def type_check_elim (e : Elim) (expected_type : Term) (scope : Scope)
    (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match e {
        { inductive := inductive, levels := _, params := params, indices := indices,
          motive := _, minors := _, scrutinee := scrutinee } =>
            match scope_find_inductive inductive scope {
                err _ => err (TypeError.custom
                    (String.concat "Term.elim: unknown inductive " (show_name_path inductive))),
                ok ind =>
                    match type_check scrutinee Term.hole scope local_types locals {
                        err err_ => err err_,
                        ok sc_tt =>
                            // R4c: `indices` extends the scrutinee's own
                            // claimed type spine alongside `params` --
                            // `Eq T x y`'s full spine is `params ++
                            // indices = [T, x] ++ [y]`, not `params` alone.
                            let expected_scrutinee_typ : Term :=
                                rebuild_call (free_var_ref inductive) (List.append params indices) in
                            match unify sc_tt.typ expected_scrutinee_typ scope locals {
                                err err_ => err err_,
                                ok _ =>
                                    type_check_elim_motive e ind sc_tt.term sc_tt.typ
                                        expected_type scope local_types locals,
                            },
                    },
            },
    }

/// Checks `e`'s motive infers to a function into a sort, its domain
/// agreeing with the scrutinee's real type -- the
/// `type_check_pathp_go`/`type_check_hcomp_go` pattern, generalized from
/// the interval/a type to an arbitrary inductive's instantiated type.
/// Destructured for the same reason `type_check_elim` above is.
///
/// `#[terminating]`: same reason as `type_check_elim`'s own annotation --
/// the call into `type_check_elim_minors` carries extra accumulated
/// arguments (`motive_tt.term`, `sc_term`, `sc_typ`) that break the
/// automatic positional check, even though `motive` is a genuine subterm
/// of `e` (the plain `type_check motive ...` call just above finds that
/// decrease automatically, same arity, no annotation needed there).
#[terminating]
def type_check_elim_motive (e : Elim) (ind : Inductive) (sc_term : Term) (sc_typ : Term)
    (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope)
    : Result TypeError TypedTerm :=
    match e {
        { inductive := _, levels := _, params := _, indices := indices, motive := motive,
          minors := _, scrutinee := _ } =>
            match type_check motive Term.hole scope local_types locals {
                err err_ => err err_,
                ok motive_tt =>
                    match type_check_elim_motive_pis indices motive_tt.typ sc_typ scope
                        local_types locals {
                        err err_ => err err_,
                        ok cod =>
                            match sort_level_of cod {
                                Option.none => err (TypeError.custom
                                    "Term.elim's motive must be a function into a sort"),
                                Option.some _l =>
                                    type_check_elim_minors e ind motive_tt.term sc_term
                                        sc_typ expected_type scope local_types locals,
                            },
                    },
            },
    }

/// Peels one `Term.pi` per entry in `indices`, checking each index TERM's
/// own inferred type against that Pi's domain (the same "infer, then
/// unify against the motive's own declared domain" shape the scrutinee
/// itself already gets, generalized from one argument to `K+1`), then
/// peels one final `Pi` for the scrutinee itself -- R4's own original
/// rule, unchanged, once `indices` is empty. Returns the final codomain
/// for the caller's own sort check, same contract `term_peel`'s result
/// had before this generalized it.
///
/// **Must `beta_reduce` the peeled codomain against the ACTUAL index
/// term before continuing**, not pass it through raw -- confirmed as a
/// real bug, not a style choice, by actually running a genuinely
/// dependent two-argument motive (`(x:P) -> MyEq P p0 x -> Sort 1`): the
/// SECOND Pi's own domain (`MyEq P p0 x`) still mentions `x` as a BOUND
/// variable until the first index's own concrete value is substituted in
/// for it, exactly the same "apply a dependent Pi to its argument"
/// semantics `beta_reduce` already exists for -- an unsubstituted `cod`
/// made the base case's `unify sc_typ dom` compare a concrete scrutinee
/// type against a domain that still contained a dangling bound variable,
/// failing even on a genuinely correct motive.
///
/// `#[terminating]`: `motive_typ` is this def's SECOND parameter, so the
/// recursive call (which passes the PEELED, SUBSTITUTED codomain, not a
/// subterm of `indices`) cannot be seen as a structural decrease on
/// `indices` alone by the automatic checker -- `indices` itself IS still
/// strictly decreasing (`irest`), which is the real reason this
/// terminates.
#[terminating]
def type_check_elim_motive_pis (indices : List Term) (motive_typ : Term) (sc_typ : Term)
    (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError Term :=
    match indices {
        List.empty =>
            match term_peel motive_typ {
                Term.pi _b dom cod =>
                    match unify sc_typ dom scope locals {
                        err err_ => err err_,
                        ok _ => ok cod,
                    },
                _ => err (TypeError.custom "Term.elim's motive must be a function"),
            },
        List.cons idx irest =>
            match term_peel motive_typ {
                Term.pi _b dom cod =>
                    match type_check idx Term.hole scope local_types locals {
                        err err_ => err err_,
                        ok idx_tt =>
                            match unify idx_tt.typ dom scope locals {
                                err err_ => err err_,
                                ok _ =>
                                    type_check_elim_motive_pis irest (beta_reduce cod idx_tt.term)
                                        sc_typ scope local_types locals,
                            },
                    },
                _ => err (TypeError.custom "Term.elim's motive must be a function"),
            },
    }

/// Checks every minor against its own constructor applied to the
/// motive, then computes the elim's own type as the motive applied to
/// the (real, checked) scrutinee -- unified against `expected_type`
/// exactly as every other `type_check_*` rule in this file does at its
/// own exit.
///
/// `#[terminating]`: same reason as `type_check_elim`'s own annotation --
/// the call into `type_check_elim_minors_go` reorders/adds arguments
/// (`inductive_constructors ind`, `e.minors` ahead of `ind`/`sc_typ`/
/// `motive_term`) relative to this def's own parameter list, breaking the
/// automatic positional check even though the actual recursion
/// (`type_check_elim_minors_go` itself, then `type_check_elim_minor`) is
/// plain list-structural recursion needing no annotation of its own.
#[terminating]
def type_check_elim_minors (e : Elim) (ind : Inductive) (motive_term : Term) (sc_term : Term)
    (sc_typ : Term) (expected_type : Term) (scope : Scope) (local_types : List Term)
    (locals : LocalScope) : Result TypeError TypedTerm :=
    let actual_args : List Term := List.append e.params e.indices in
    let num_params : I64 := List.length e.params in
    match type_check_elim_minors_go (inductive_constructors ind) e.minors ind actual_args
        num_params sc_typ motive_term scope local_types locals {
        err err_ => err err_,
        ok checked_minors =>
            // The elim's own type: motive applied to EVERY index, then the
            // (real, checked) scrutinee -- `motive y e` for `Eq.rec`, not
            // just `motive e`. `rebuild_call` generalizes the plain
            // `Term.app motive_term sc_term` this was before R4c.
            let elim_typ : Term :=
                rebuild_call motive_term (List.append e.indices (List.cons sc_term List.empty)) in
            match unify elim_typ expected_type scope locals {
                err err_ => err err_,
                ok unified =>
                    ok (mk_typed
                        (Term.elim { e with motive := motive_term, minors := checked_minors, scrutinee := sc_term })
                        unified),
            },
    }

/// Walks `ind`'s constructors and `e.minors` in lockstep -- both
/// positional in the inductive's declared order, the same invariant
/// `build_elim_minors` (R3b) already relies on to CONSTRUCT an `Elim`'s
/// minors. A length mismatch either way is a real arity error, not a
/// partial-information fallback: unlike `arg_types_for_case`'s `Option
/// Inductive`, `ind` here is always resolved (R4's caller already erred
/// out if it wasn't).
def type_check_elim_minors_go (ctors : List InductConstructor) (minors : List Term) (ind : Inductive)
    (actual_args : List Term) (num_params : I64) (sc_typ : Term) (motive_term : Term) (scope : Scope)
    (local_types : List Term) (locals : LocalScope) : Result TypeError (List Term) :=
    match ctors {
        List.empty =>
            match minors {
                List.empty => ok List.empty,
                List.cons _ _ => err (TypeError.custom
                    "Term.elim has more minors than its inductive has constructors"),
            },
        List.cons ctor crest =>
            match minors {
                List.empty => err (TypeError.custom
                    "Term.elim is missing a minor for a constructor"),
                List.cons minor mrest =>
                    match type_check_elim_minor ctor minor ind actual_args num_params sc_typ motive_term
                        scope local_types locals {
                        err err_ => err err_,
                        ok checked_minor =>
                            match type_check_elim_minors_go crest mrest ind actual_args num_params
                                sc_typ motive_term scope local_types locals {
                                err err_ => err err_,
                                ok checked_rest => ok (List.cons checked_minor checked_rest),
                            },
                    },
            },
    }

/// One minor's expected type is a Pi-chain over its constructor's own
/// (instantiated) field types, ending in the motive applied to that
/// constructor applied to those same fields -- `motive (K x1 ... xn)`.
/// `motive_term` is shifted by the field count ONCE before use, the same
/// discipline `elim_minor_for_ctor`'s wildcard case (R3b) already
/// documents: it is moving under `n` new binders it does not itself
/// reference. Checking the written `minor` (a lambda chain,
/// `build_named_lambda_chain`/`build_anon_lambda_chain`'s own output
/// shape) against this Pi-chain reuses `type_check_lam`'s existing
/// bidirectional rule at every level -- no new per-field logic.
///
/// `#[terminating]`: same reason as `type_check_elim`'s own annotation --
/// `minor` is this def's SECOND parameter, not its first, so the call
/// into `type_check minor expected_minor_typ ...` passes `minor` at a
/// different position than this def's own params are checked against,
/// which the automatic positional decrease check cannot see past (it is
/// not reordering `type_check`'s call, only misaligning it against this
/// def's own signature).
#[terminating]
def type_check_elim_minor (ctor : InductConstructor) (minor : Term) (ind : Inductive)
    (actual_args : List Term) (num_params : I64) (sc_typ : Term)
    (motive_term : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope)
    : Result TypeError Term :=
    let field_types : List Term := substitute_inductive_type_params ind sc_typ (types_from_params ctor.params) in
    let n : I64 := List.length field_types in
    let ctor_app : Term := rebuild_call (free_var_ref ctor.name) (elim_field_vars field_types (n - 1)) in
    let shifted_motive : Term := term_shift n motive_term in
    // R4c: this constructor's OWN index value(s), not the caller's generic
    // `indices` -- `refl`'s own minor is checked against `motive a
    // (refl)`, not `motive y (refl)`, the same way an ordinary dependent
    // pattern-match arm's expected type uses THAT branch's own refined
    // index, not the scrutinee's pre-refinement one. `n`-shifted for the
    // same reason `shifted_motive`/`ctor_app` already are: these values
    // are built from OUTER-context data now sitting under `n` new binders
    // the Pi-chain just introduced.
    let ctor_indices : List Term := terms_shift n (ctor_index_values ind actual_args num_params ctor) in
    let expected_minor_typ : Term :=
        build_elim_minor_pi_chain field_types
            (rebuild_call shifted_motive (List.append ctor_indices (List.cons ctor_app List.empty))) in
    match type_check minor expected_minor_typ scope local_types locals {
        err err_ => err err_,
        ok minor_tt => ok minor_tt.term,
    }

/// This constructor's own concrete index value(s) (R4c) -- substitute the
/// inductive's own declared params into THIS ctor's own declared return
/// type (`ctor.typ`, which the parser keeps verbatim for an explicitly
/// annotated constructor like `refl : Eq A a a` -- confirmed directly,
/// not assumed, see the R4c reconnaissance in `core-term-
/// simplification.md`), using the SAME actual-argument list (`e.params ++
/// e.indices`) that instantiates the whole `Elim`, then read off
/// everything in the result's own spine PAST the `params` portion. Pure
/// by-name substitution, reusing `substitute_inductive_type_params`'s own
/// established technique (generalized from a `List Term` of field types
/// to one return-type term) -- no unification, no arithmetic, which is
/// exactly the scope line that reconnaissance draws: this only works when
/// a constructor's own return type specializes an index via an
/// ALREADY-BOUND name (`Eq.refl`'s `a`), never an expression depending on
/// that SAME constructor's own fields (`Vec`'s `cons : ... -> Vec A
/// (n+1)`, out of scope, same unaddressed gap `implementations/field-
/// pattern-type-args-not-substituted.md` already names).
def ctor_index_values (ind : Inductive) (actual_args : List Term) (num_params : I64)
    (ctor : InductConstructor) : List Term :=
    let substituted : Term := substitute_inductive_params_into ind.params actual_args ctor.typ in
    match flatten_call_spine substituted {
        CallSpine.mk _head args => drop_n num_params args,
    }

/// Substitute the inductive's own declared params into ONE term (`ctor.
/// typ`), by name -- the single-term twin of `substitute_inductive_type_
/// params_go`'s own `List Term` walk, needed because a constructor's
/// return type is one term, not a field-type list. `p.name` by dot
/// access, not `Param.mk pname _ _ _ _` positionally -- the style
/// ratchet's `wide_positional_pattern_violation` counter flags a wide
/// positional match against a NAMED-field struct like `Param`, even
/// though `substitute_inductive_type_params_go` (just below) already does
/// this the positional way; copying that existing idiom into a brand-new
/// function was confirmed (not assumed) to regress the ratchet, fixed by
/// not repeating it rather than by excusing a second instance.
#[terminating]
def substitute_inductive_params_into (ind_params : List Param) (actual_args : List Term) (t : Term) : Term :=
    match ind_params {
        List.cons p prest =>
            match actual_args {
                List.cons a arest =>
                    substitute_inductive_params_into prest arest (name_subst_term p.name a t),
                List.empty => t,
            },
        List.empty => t,
    }

/// Drop the first `n` elements of `xs` -- `std`'s own `List` carries no
/// `drop` (confirmed: grepped the whole tree, the only `.drop` is
/// `String.drop`), so this is a small hand-rolled twin, same convention
/// `elim_field_vars`/`substitute_inductive_type_params_go` already use
/// for a brand-new list op in this file.
#[terminating]
def drop_n (n : I64) (xs : List Term) : List Term :=
    if I64.beq n 0 then xs
    else match xs {
        List.cons _ rest => drop_n (n - 1) rest,
        List.empty => List.empty,
    }

/// `term_shift d` over every element of a list -- needed because a
/// constructor's own computed index values (`ctor_index_values`) are
/// built from OUTER-context data and must be re-scoped the same way
/// `shifted_motive`/`ctor_app` already are once placed under the Pi-
/// chain's `n` new field binders.
#[terminating]
def terms_shift (d : I64) (ts : List Term) : List Term :=
    match ts {
        List.empty => List.empty,
        List.cons t rest => List.cons (term_shift d t) (terms_shift d rest),
    }

/// `[var(n-1), var(n-2), ..., var(0)]` for `n = List.length field_types`
/// -- declared-field order, OUTERMOST binder first, matching
/// `whnf_subst_case_fields`'s documented convention (R3b's own doc
/// comment cites it). Recurses on `field_types` itself (not a raw `I64`
/// countdown) so the termination checker sees the same structural
/// decrease `build_anon_lambda_chain` already relies on.
def elim_field_vars (field_types : List Term) (idx : I64) : List Term :=
    match field_types {
        List.empty => List.empty,
        List.cons _ trest => List.cons (Term.var idx DebugName.unnamed) (elim_field_vars trest (idx - 1)),
    }

/// One `Term.pi` per field type, OUTERMOST first, ending in `body` --
/// the Pi-chain counterpart to `build_anon_lambda_chain` (R3b), used to
/// state a minor's EXPECTED type rather than construct one.
def build_elim_minor_pi_chain (field_types : List Term) (body : Term) : Term :=
    match field_types {
        List.empty => body,
        List.cons t trest => Term.pi binder_anon t (build_elim_minor_pi_chain trest body),
    }

// ─── R3b: elaboration into `Elim` (core-term-simplification.md) ──────────
//
// `elaborate_if_to_elim`/`elaborate_match_to_elim` build the `Term.elim`
// that an `if`/`match` COULD be, with a CONSTANT motive -- the same
// non-dependent result `type_check_if`/`type_check_match` already produce
// today. Deliberately NOT called from either of those yet: that is R3c,
// gated on R4, since the checker has no typing rule for `Elim` with a
// real motive until then, and wiring this in early would make every
// `if`/`match` uncheckable. Exercised directly by pins in
// `lang/src/tests/infer_tests.mo` instead.

/// `if c t e` as an `Elim` on `Bool`: two nullary constructors, so each
/// minor is its branch TERM unchanged -- no lambda wrapping needed, the
/// same reason `type_check_if` never builds a `MatchCase` today.
/// `bool_ind` is the caller's to resolve (R3c would do this once, the
/// way `type_check_match` resolves an inductive via `validate_match_
/// constructors` today); this function assumes it already IS `Bool`'s
/// real `Inductive`, `true` before `false` in `constructors`
/// (`init/src/prelude.mo`'s own declaration order), and does no
/// resolution of its own.
///
/// `motive` ignores the scrutinee -- both branches already share one
/// `result_typ` by the time `type_check_if` has unified `two`/`three`
/// against each other, so a constant function `Bool -> Sort l`
/// reproduces today's non-dependent result exactly. `term_shift 1` is
/// what keeps `result_typ` well-scoped under the motive's own new
/// binder, which it does not reference.
def elaborate_if_to_elim (bool_ind : Inductive) (cond : Term) (then_term : Term)
    (else_term : Term) (result_typ : Term) : Term :=
    let bool_typ : Term := named_type_ref "Bool" in
    let motive : Term := Term.lam binder_anon bool_typ (term_shift 1 result_typ) in
    let minors : List Term := List.cons then_term (List.cons else_term List.empty) in
    Term.elim (Elim.mk bool_ind.name List.empty List.empty List.empty motive minors cond)

/// `match value_ { ... }` as an `Elim`, with a constant motive -- same
/// non-dependent reproduction as `elaborate_if_to_elim` above,
/// generalized to any inductive and any arity. `checked_cases` must
/// already be the TYPE-CHECKED case list `type_check_cases` returns
/// (field patterns resolved, each case's `args` in ITS OWN
/// constructor's declared field order -- `term_permute`'s job, already
/// done): this function does no resolution of its own, exactly mirroring
/// how `Literal.match_ scrutinee_term checked_cases` is itself built from
/// that same list (`type_check_cases`, above). `ind` must be the
/// scrutinee's real resolved `Inductive`; a `match` whose inductive could
/// not be resolved (`maybe_ind = Option.none`) has no `Elim` this
/// function can build and stays on the old `Literal.match_` path at R3c,
/// same as every other partial-information fallback in this file.
def elaborate_match_to_elim (ind : Inductive) (scrutinee_typ : Term) (scrutinee_term : Term)
    (checked_cases : List MatchCase) (result_typ : Term) : Term :=
    let params : List Term := match flatten_call_spine scrutinee_typ { CallSpine.mk _head args => args } in
    let motive : Term := Term.lam binder_anon scrutinee_typ (term_shift 1 result_typ) in
    let maybe_ind : Option Inductive := Option.some ind in
    let minors : List Term := build_elim_minors (inductive_constructors ind) checked_cases scrutinee_typ maybe_ind in
    Term.elim (Elim.mk ind.name List.empty params List.empty motive minors scrutinee_term)

/// One minor per constructor, in `ind`'s own DECLARATION order -- not
/// `cases`' written order, which `missing_constructors_go` below already
/// deliberately ignores for the same reason (coverage is a set test, not
/// a positional one).
def build_elim_minors (ctors : List InductConstructor) (cases : List MatchCase)
    (scrutinee_typ : Term) (maybe_ind : Option Inductive) : List Term :=
    match ctors {
        List.empty => List.empty,
        List.cons ctor rest =>
            List.cons
                (elim_minor_for_ctor ctor cases scrutinee_typ maybe_ind)
                (build_elim_minors rest cases scrutinee_typ maybe_ind),
    }

/// The one minor this constructor contributes: built from the first case
/// (in WRITTEN order) that covers it -- a real named arm, or a `_` that
/// reaches it. `Option.none` is unreachable once `validate_match_
/// coverage` (strict-exhaustiveness.md Phase 4, now a hard error) has
/// run over this same `cases`/`ind` pair before elaboration ever gets
/// here; `Term.hole` is a backstop for a caller that skipped that check,
/// never something a checked program can reach.
def elim_minor_for_ctor (ctor : InductConstructor) (cases : List MatchCase)
    (scrutinee_typ : Term) (maybe_ind : Option Inductive) : Term :=
    match ctor {
        InductConstructor.mk cname _cparams _ctyp =>
            match find_covering_case cname cases {
                Option.none => Term.hole,
                Option.some case_ =>
                    if match_is_wildcard_name case_.name
                    then
                        let field_types : List Term :=
                            arg_types_for_case (constructor_bare_name cname) maybe_ind scrutinee_typ in
                        build_anon_lambda_chain field_types (term_shift (List.length field_types) case_.body)
                    else
                        let field_types : List Term := arg_types_for_case case_.name maybe_ind scrutinee_typ in
                        build_named_lambda_chain case_.args field_types case_.body,
            },
    }

/// First case (written order) that covers `cname` -- an explicit arm by
/// name, or `_` (which covers every constructor it reaches, by
/// definition). Mirrors `case_names_cover_constructor`'s per-constructor
/// predicate below, but returns the CASE itself rather than a `Bool`,
/// since the caller needs its `args`/`body`, not just whether one
/// exists.
def find_covering_case (cname : NamePath) (cases : List MatchCase) : Option MatchCase :=
    match cases {
        List.empty => Option.none,
        List.cons hd rest =>
            if match_is_wildcard_name hd.name || case_name_covers hd.name cname
            then Option.some hd
            else find_covering_case cname rest,
    }

/// Wrap `body` in one `Term.lam` per `(name, type)` pair, OUTERMOST
/// first -- `names[0]` ends up at the HIGHEST de Bruijn index, matching
/// how a written case's `args`/`body` are already bound
/// (`whnf_subst_case_fields`'s own doc comment: "the outermost binder
/// sits at de Bruijn index n-1"), so no reindexing of `body` is needed,
/// only real `Term.lam` nodes where there were none.
def build_named_lambda_chain (names : List Identifier) (types : List Term) (body : Term) : Term :=
    match names {
        List.empty => body,
        List.cons n nrest =>
            match types {
                List.cons t trest => Term.lam (binder_named n) t (build_named_lambda_chain nrest trest body),
                List.empty => Term.lam (binder_named n) Term.hole (build_named_lambda_chain nrest List.empty body),
            },
    }

/// Same shape as `build_named_lambda_chain`, for a constructor a `_` arm
/// covers: there are no written names for its fields, so every binder is
/// `binder_anon`. The one call site above (`elim_minor_for_ctor`) shifts
/// the wildcard arm's `body` by the FULL field count ONCE, before calling
/// this -- it is moving under that many new binders it does not
/// reference, and shifting once rather than once per level is exactly as
/// correct, since nothing between the shift and the outermost new binder
/// references the shifted indices.
def build_anon_lambda_chain (types : List Term) (body : Term) : Term :=
    match types {
        List.empty => body,
        List.cons t trest => Term.lam binder_anon t (build_anon_lambda_chain trest body),
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
///
/// A location wrapper is transparent here, and the `Term.ctx` arm is what
/// makes that structural rather than a per-call-site obligation (R10,
/// plans/type-system/core-term-simplification.md). It matters because
/// this function's `Option.none` is not an error -- it is a fallback to
/// an ambiguous constructor-name scan -- so a wrapper that stops the
/// match does not crash or fail to type: it makes an inductive resolve by
/// the WRONG path. Placement rule R1 keeps wrappers out of type position
/// (`lower_parse_term_bare`), which is why this has not been seen live;
/// `class FromListLiteral` (`term_matches_carrier`'s own doc comment) is
/// the measured regression from the one site that did not have that
/// guarantee. The arm is the guarantee.
def type_head_name (t : Term) : Option Identifier :=
    match t {
        Term.ctx _loc inner => type_head_name inner,
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
            match scope_find_inductive (NamePath.mk (List.cons id List.empty)) scope {
                // Cross-check the cases before committing, exactly as the
                // `con_owner_name` path above already does -- `type_head_
                // name` yields a BARE name and `scope_find_inductive` keys
                // on bare names too, so in a whole-program scope (codegen's
                // `build_scope_from_decls` over every loaded module at once,
                // unlike `check`'s per-target scope) two modules declaring
                // the same type name are indistinguishable here and the
                // winner is decided by module load order.
                //
                // `lang/types.mo`'s `Decl` and `init/meta.mo`'s `Decl` are
                // exactly such a pair. When the latter won, `lang/scope.mo`'s
                // `infix_from_decl` -- `match d { Decl.infix_d ... }` --
                // committed to an inductive whose constructors are `d_def`/
                // `d_instance`/`d_error` and died on `validate_cases_against_
                // inductive`'s "constructor not found in inductive", with
                // `elaborate_module_decls_best_effort` then keeping the
                // un-elaborated decl and `validate_no_undesugared_struct_
                // lits` rejecting the struct literal it still contained.
                // Which `Decl` won flipped purely on an unrelated `use` list
                // change in `cli/src/main.mo`.
                //
                // Falling through instead reaches the constructor-name scan
                // (`find_inductive_for_cases_by_constructor`), which keys on
                // the cases' own constructors and so picks the inductive the
                // match is actually about.
                ok ind =>
                    match validate_cases_against_inductive cases ind {
                        ok _ => ok (Option.some ind),
                        err _ => find_inductive_by_call_return_type_or_scan cases scrutinee_term scope,
                    },
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
            match scope_find_def_return_type (NamePath.mk (List.cons id List.empty)) scope {
                Option.some ret_typ =>
                    match type_head_name ret_typ {
                        Option.some tid =>
                            match scope_find_inductive (NamePath.mk (List.cons tid List.empty)) scope {
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
/// Peels, at entry and therefore through the `Term.app` recursion too. A
/// match SCRUTINEE is located (`lower_parse.mo` lowers `Literal.match_`'s
/// scrutinee with `lower_parse_term`, not `_bare`), so without this every
/// `match <bare call> { .. }` lost the "resolve the inductive from the
/// call's declared return type" path and fell through to
/// `find_inductive_for_cases_by_constructor`, which reports a genuine
/// ambiguity rather than guessing -- `ambiguous constructor `cons`: could
/// resolve to either `Vec` or `List`` on `init/tests.mo`, caught by
/// `slow_tests/typecheck_init_tests.mo` once located terms reached the
/// checker on every path.
///
/// `#[terminating]`: peeling at entry means `f` is a structural subterm of
/// `term_peel t` rather than of `t`, which the checker cannot see through.
/// It is well-founded -- `term_peel` strictly removes wrappers, and the
/// `Term.app` recursion strictly descends.
#[terminating]
def call_head_def_name (t : Term) : Option Identifier :=
    match term_peel t {
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

/// Find the `NamePath` naming a scrutinee term's owning inductive,
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
///   and treat it as a one-segment `NamePath`. This is the arm that
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
/// Peels, for the same reason `call_head_def_name` above does: a match
/// SCRUTINEE is located, and a bare constructor application like
/// `Vec.cons 42 Vec.nil` is exactly the shape this arm-chain exists to
/// recognise. Unpeeled it fell to `_ => Option.none` and the resolution
/// dropped to the constructor-name scan, which reports the collision this
/// function was added to fix: `ambiguous constructor `cons`: could resolve
/// to either `Vec` or `List``, on `init/tests.mo`.
///
/// `#[terminating]` for the same reason as `call_head_def_name`: peeling at
/// entry hides `f`'s structural descent from the checker.
#[terminating]
def con_owner_name (t : Term) : Option NamePath :=
    match term_peel t {
        Term.con c => match c { Con.mk _ typ_name _ _ => Option.some typ_name },
        Term.app f _ => con_owner_name f,
        Term.var _ dbg =>
            match dbg {
                DebugName.named id =>
                    match id {
                        Identifier.id s =>
                            match dotted_qualifier s {
                                Option.some qual => Option.some (NamePath.mk (List.cons (Identifier.id qual) List.empty)),
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
///
/// Pub because the check path's coverage-warning collector
/// (`lang/module.mo`) resolves a match's inductive exactly this way --
/// same fallback, same ambiguity behavior -- so the two cannot drift
/// about which match a gap is reported for.
pub def find_inductive_for_cases_by_constructor (cases : List MatchCase) (scope : Scope) : Result TypeError (Option Inductive) :=
    match cases {
        List.empty => ok Option.none,
        List.cons hd rest =>
            match hd {
                MatchCase.mk name _ _ _ _ =>
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
                        let con_mp : NamePath := NamePath.mk (List.cons name List.empty) in
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
        Inductive.mk name _ _ _ _ _ => show_name_path name,
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
                MatchCase.mk name _ _ fp _ =>
                    let wildcard_id : Identifier := Identifier.id "_" in
                    match fp {
                        Option.some _ => validate_cases_against_inductive rest ind,
                        Option.none =>
                            if Similar.similar name wildcard_id
                            then validate_cases_against_inductive rest ind
                            else
                                let con_mp : NamePath := NamePath.mk (List.cons name List.empty) in
                                if inductive_has_constructor ind con_mp
                                then validate_cases_against_inductive rest ind
                                else err (TypeError.custom "constructor not found in inductive"),
                    },
            },
    }

// --- Match exhaustiveness (strict-exhaustiveness.md, Phase 1) ---
//
// A match must cover every constructor of its scrutinee's inductive. Before
// this the self-hosted checker reported NOTHING for a missing arm, and the
// backend compensated by making the LAST arm unconditional
// (`build_match_chain`, lang/codegen/emit.mo) -- so a match omitting `T.e`
// silently ran `T.d`'s body and returned a wrong value. That shipped once:
// plans/implementations/2026-08-29-native-io-op-non-exhaustive-match-crash.md.
//
// Coverage is deliberately a plain TOP-LEVEL constructor-coverage test, not a
// usefulness/full-pattern algorithm. Measured over the whole corpus (6725
// matches, 237 files): 0 nested patterns, 0 literal patterns, 0 tuple
// patterns, 0 guards, 0 duplicate arms, 0 arms after a catch-all -- there is
// nothing for a general algorithm to be more precise about.

/// `` `T.d` `` -- the constructor qualified by its OWN inductive's name.
/// The qualifier is not decoration: `InductConstructor.mk`'s own `NamePath`
/// is never type-prefixed (`constructor_bare_name`), so rendering it bare
/// would print `` `d` `` for every type that has a `d` -- and
/// `init/prelude.mo` really does declare both `List` and `Vec` with a
/// `cons`.
def quoted_ctor_path (ty : String) (np : NamePath) : String :=
    "`" ++ ty ++ "." ++ show_identifier (constructor_bare_name np) ++ "`"

/// `` `T.d`, `T.e` `` -- the missing constructors backticked and comma
/// separated, in the caller's order (which is the inductive's DECLARATION
/// order). Determinism matters here: the check-plan cache keys on the
/// diagnostic text, so the same file must render byte-identically.
def missing_ctor_names_joined (ty : String) (missing : List NamePath) : String :=
    match missing {
        List.empty => "",
        List.cons hd rest =>
            match rest {
                List.empty => quoted_ctor_path ty hd,
                List.cons _ _ =>
                    String.concat (quoted_ctor_path ty hd)
                        (String.concat ", " (missing_ctor_names_joined ty rest)),
            },
    }

def non_exhaustive_match_message (ind : Inductive) (missing : List NamePath) : String :=
    let listed : String := missing_ctor_names_joined (inductive_name_str ind) missing in
    if I64.beq (List.length missing) 1
    then "non-exhaustive match: " ++ listed ++ " is not covered (add an arm for it, or a `_` arm)"
    else "non-exhaustive match: " ++ listed ++ " are not covered (add arms for them, or a `_` arm)"

def inductive_constructors (ind : Inductive) : List InductConstructor :=
    match ind { Inductive.mk _name _params _typ constructors _attrs _vis => constructors }

/// Whether a case's own name is the `_` wildcard, spelled once
/// (`wildcard_binder_name`) rather than re-derived here.
def match_is_wildcard_name (name : Identifier) : Bool :=
    Similar.similar name wildcard_binder_name

/// Whether some case is `_`. A wildcard covers every constructor by
/// definition, so `uncovered_constructors` returns before its walk.
def match_has_wildcard_case (cases : List MatchCase) : Bool :=
    match cases {
        List.empty => false,
        List.cons hd rest =>
            match hd {
                MatchCase.mk name _ _ _ _ =>
                    if match_is_wildcard_name name then true else match_has_wildcard_case rest,
            },
    }

/// Whether the case named `name` covers the constructor `cname` -- compared
/// by BARE name, because `InductConstructor.mk`'s own `NamePath` is never
/// type-prefixed while a written case names only the last segment
/// (`constructor_bare_name`). A `_` case never reaches here (the
/// short-circuit above); the parser's `""` bare-field-pattern placeholder
/// matches nothing, which is over-reporting in the safe direction --
/// deliberately the OPPOSITE of `find_inductive_for_cases_by_constructor`'s
/// treatment of `""`, where the question is which name to scan BY, not what
/// is covered.
def case_name_covers (name : Identifier) (cname : NamePath) : Bool :=
    id_eq name (constructor_bare_name cname)

def case_names_cover_constructor (cases : List MatchCase) (cname : NamePath) : Bool :=
    match cases {
        List.empty => false,
        List.cons hd rest =>
            match hd {
                MatchCase.mk name _ _ _ _ =>
                    if case_name_covers name cname then true
                    else case_names_cover_constructor rest cname,
            },
    }

def missing_constructors_go (cases : List MatchCase) (ctors : List InductConstructor) (acc : List NamePath) : List NamePath :=
    match ctors {
        List.empty => list_reverse acc,
        List.cons ctor rest =>
            match ctor {
                InductConstructor.mk cname _params _typ =>
                    if case_names_cover_constructor cases cname
                    then missing_constructors_go cases rest acc
                    else missing_constructors_go cases rest (List.cons cname acc),
            },
    }

/// `ind`'s constructors that no case of `cases` covers, in declaration order;
/// empty when a `_` case is present.
///
/// An inductive with NO constructors (`Void`, the primitives, the synthetic
/// `Type`/`Prop`/`Sort`/`Pred`) has nothing to cover, so this is vacuously
/// empty and every match on one passes. Do NOT invert that into "0
/// constructors requires an empty match" -- that rule is the hazard; this one
/// needs no special case for them precisely because it is phrased as "every
/// constructor is covered".
def uncovered_constructors (cases : List MatchCase) (ind : Inductive) : List NamePath :=
    if match_has_wildcard_case cases
    then List.empty
    else missing_constructors_go cases (inductive_constructors ind) List.empty

/// The rule. `maybe_ind = Option.none` PASSES, and that is the honest hole:
/// the scrutinee's type could not be resolved, which is frequent and genuine,
/// and rejecting it would red the corpus at scale while STILL being unsound
/// (it would reject provably exhaustive matches the resolver missed). Phase
/// 2's per-tag runtime trap (lang/codegen/emit.mo) closes that hole at run
/// time, on the tag actually computed, needing no static type at all.
///
/// A def marked `#[allow_incomplete_match "<reason>"]` opts out via
/// `Scope.incomplete_match_ok` (set in lang/module.mo; see
/// `has_incomplete_match_exemption`).
///
/// THIS IS NOW AN ERROR (strict-exhaustiveness.md Phase 4, flipped once the
/// corpus was swept clean). It used to be a deliberate warning, because
/// returning `err` reached codegen through `elaborate_def_with_scope`, whose
/// caller (`elaborate_module_decls_reporting`, lang/module.mo) is
/// best-effort and SWALLOWED the error, leaving the def un-elaborated for
/// codegen's syntactic fallbacks to miscompile into a SIGSEGV with no
/// diagnostic (`lang/codegen/validate.mo` documents that exact shape; it
/// cost a ladder rung on 2026-10-06). `scope_for_elab_body` (lang/module.mo)
/// still forces `incomplete_match_ok := true` unconditionally, so that path
/// stays exempt by design -- only `check` (via `check_def_with_scope`)
/// enforces this rule now. `match_coverage_warning` below is the reporting
/// half and renders the same message this now returns.
def validate_match_coverage (cases : List MatchCase) (maybe_ind : Option Inductive) (scope : Scope) : Result TypeError Bool :=
    match match_coverage_gap cases maybe_ind scope {
        Option.some p => match p {
            Pair.pair ind missing => err (TypeError.custom (non_exhaustive_match_message ind missing)),
        },
        Option.none => ok true,
    }

/// The rule as a pure QUERY: the uncovered constructors of this match, or
/// `Option.none` when it is covered, unresolved, or exempted. One place, so
/// the check that warns and a future check that errors cannot disagree about
/// what "uncovered" means -- the same single-source-of-truth reason the host
/// computes its `use`-completeness findings in one function
/// (`unimported_names`, `core/src/term/module.rs`).
pub def match_coverage_gap (cases : List MatchCase) (maybe_ind : Option Inductive) (scope : Scope) : Option (Pair Inductive (List NamePath)) :=
    if scope.incomplete_match_ok then Option.none
    else match maybe_ind {
        Option.none => Option.none,
        Option.some ind =>
            let missing : List NamePath := uncovered_constructors cases ind in
            match missing {
                List.empty => Option.none,
                List.cons _ _ => Option.some (Pair.pair ind missing),
            },
    }

/// The warning text for a coverage gap, or `Option.none` when there is none.
/// The message is prefix-free; the severity word comes from the renderer
/// (`render_type_warning`, lang/typecheck/diagnostic.mo).
pub def match_coverage_warning (cases : List MatchCase) (maybe_ind : Option Inductive) (scope : Scope) : Option String :=
    match match_coverage_gap cases maybe_ind scope {
        Option.none => Option.none,
        Option.some p => match p {
            Pair.pair ind missing => Option.some (non_exhaustive_match_message ind missing),
        },
    }

/// Type check match cases — process all cases and unify their body types.
def type_check_cases (cases : List MatchCase) (scrutinee_term : Term) (scrutinee_typ : Term) (maybe_ind : Option Inductive) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match type_check_cases_accum cases scrutinee_term scrutinee_typ maybe_ind expected_type scope local_types locals (Term.hole) List.empty {
        ok acc =>
            match acc {
                mk body_typ checked_cases =>
                    match unify body_typ expected_type scope locals {
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
                                    match unify acc_typ body_typ scope locals {
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
            // Coverage is checked HERE rather than in
            // `validate_match_constructors` (which runs before any arm is
            // checked): only by now is every arm either a `_` or a real
            // resolved constructor name, because
            // `type_check_field_pattern_case` rewires a field-pattern arm
            // into `MatchCase.mk resolved_name ... Option.none`. That is also
            // what makes a field pattern cover its constructor for free.
            match validate_match_coverage reversed maybe_ind scope {
                err e => err e,
                ok _ =>
                    // Annotated local first -- a bare struct literal in `ok`'s
                    // argument position gets no expected type (see the matching
                    // comment in `type_check`'s `Term.hole` arm).
                    let acc : CaseAcc := { body_typ := acc_typ, cases := reversed } in
                    ok acc,
            },
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
        MatchCase.mk name args body fp _typ_name =>
            match fp {
                Option.some field_pattern =>
                    type_check_field_pattern_case name args body field_pattern scrutinee_typ maybe_ind expected_type scope local_types locals,
                Option.none =>
                    let wildcard_id : Identifier := Identifier.id "_" in
                    if Similar.similar name wildcard_id then
                        match args {
                            List.empty =>
                                type_check_case_body_checked name args body expected_type scope local_types locals maybe_ind,
                            _ =>
                                err (TypeError.custom "wildcard pattern cannot bind arguments"),
                        }
                    else
                        match args {
                            List.empty =>
                                type_check_case_body_checked name args body expected_type scope local_types locals maybe_ind,
                            _ =>
                                let arg_types : List Term := arg_types_for_case name maybe_ind scrutinee_typ in
                                let extended_types : List Term := prepend_typed args arg_types local_types in
                                let extended_locals : LocalScope := prepend_typed_local_vars args arg_types locals in
                                type_check_case_body_checked name args body expected_type scope extended_types extended_locals maybe_ind,
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
pub struct ResolvedFieldPattern {
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
def type_check_field_pattern_case (name : Identifier) (args : List Identifier) (body : Term) (fp : FieldPattern) (scrutinee_typ : Term) (maybe_ind : Option Inductive) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError CheckedCase :=
    match resolve_field_pattern_case name fp scrutinee_typ maybe_ind {
        err e => err e,
        ok resolved =>
            match resolved {
                mk resolved_name declared_names declared_types written_to_declared =>
                    let old_n : I64 := List.length args in
                    let new_n : I64 := List.length declared_names in
                    let old_depths : List I64 := old_depths_of written_to_declared old_n 0 in
                    let new_depths : List I64 := List.map (fn d => new_n - 1 - d) written_to_declared in
                    let permuted_body : Term := term_permute old_n new_n old_depths new_depths body in
                    let declared_binders : List Identifier := declared_order_binders declared_names fp in
                    let extended_types : List Term := prepend_typed declared_binders declared_types local_types in
                    let extended_locals : LocalScope := prepend_typed_local_vars declared_binders declared_types locals in
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
                    // extraction to line up -- substituting the `_`
                    // placeholder (`wildcard_binder_name`) for every
                    // `..`-discarded position, which is exactly what the
                    // IDENTICAL positional spelling (`Box.mk a _ c`) puts
                    // there, so the two spellings now elaborate to the
                    // same case. `extended_types`/`extended_locals` bind
                    // this same list, NOT `declared_names` -- see
                    // `wildcard_binder_name`'s own doc comment for the
                    // silent capture using `declared_names` there caused.
                    type_check_case_body_checked resolved_name declared_binders permuted_body expected_type scope extended_types extended_locals maybe_ind,
            },
    }

/// The `_` placeholder a `..`-discarded field pattern position binds,
/// matching what the IDENTICAL positional spelling puts there.
///
/// `binder_for_declared_field` used to fall back to the DISCARDED field's
/// own canonical name, on the documented assumption that such a position
/// is "unreachable in `body` by construction" so it "just needs to be
/// SOME valid identifier".  That assumption is false: the arm's `args`
/// become real local bindings, so a body that legitimately names an outer
/// variable called `b` -- and whose pattern discards a `Box` field also
/// called `b` -- silently resolved to the SCRUTINEE's field instead.  A
/// concrete instance: `def_apply_attrs`'s `ParseDef.mk {name, typ, term,
/// constraints, vis, ..} =>` discards `attrs` while its body reads the
/// `attrs` PARAMETER, so the rebuild returned the passed-in value
/// unchanged -- a silent no-op that stripped every `#[test]`/`#[native]`
/// attribute and made the self-hosted compiler emit no test bodies at
/// all.
///
/// `_` cannot collide with a real binding (`id_eq` compares structurally,
/// and the parser rejects `_` as a value identifier), so the two spellings
/// now elaborate to the same case.
def wildcard_binder_name : Identifier := Identifier.id "_"

/// See `type_check_field_pattern_case`'s own doc comment above for why
/// this exists -- reorders a `FieldPattern`'s written `(field, binder)`
/// entries into DECLARED-field-order binder names, using
/// `wildcard_binder_name` for a position no written entry covers (only
/// reachable via a trailing `..`).
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
        List.empty => wildcard_binder_name,
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
def resolve_field_pattern_case (case_name : Identifier) (fp : FieldPattern) (scrutinee_typ : Term) (maybe_ind : Option Inductive) : Result TypeError ResolvedFieldPattern :=
    match maybe_ind {
        Option.none => err (TypeError.custom "cannot resolve `{ .. }`: the matched value's type isn't known here"),
        Option.some ind =>
            let resolved : Result TypeError ResolvedFieldPattern :=
                if String.beq (show_identifier case_name) "" then
                    resolve_bare_field_pattern fp ind
                else
                    match find_constructor_in_inductive ind (NamePath.mk (List.cons case_name List.empty)) {
                        Option.none => err (TypeError.custom "unknown constructor in field pattern"),
                        Option.some ctor => resolve_field_pattern_against_constructor case_name ctor fp,
                    } in
            // Both branches answer the constructor's DECLARED field types,
            // still written over the inductive's own type parameters --
            // instantiate them here, once, rather than in each branch.
            match resolved {
                err e => err e,
                ok rfp => ok (rfp_substituted ind scrutinee_typ rfp),
            },
    }

/// Instantiate a resolved field pattern's declared field types with the
/// scrutinee's ACTUAL type arguments -- `p.first` on a `Pair String String`
/// binds `String`, not `Pair`'s own declared `A`.
///
/// Reuses `substitute_inductive_type_params` wholesale, which is what the
/// POSITIONAL sibling path has used since its own fix (`arg_types_for_case`,
/// below): the two match spellings now instantiate through one rule instead
/// of the field path having a second, subtly different one.
///
/// The one shape this does not reach is an INDEXED family: the substitution
/// zips the inductive's own declared params against the scrutinee's
/// application spine, so a scrutinee type argument that is not one of those
/// params (`n` of a `Vec A n`) is left alone, and a constructor whose field
/// type mentions it keeps that mention. The Rust reference solves those by
/// unifying the constructor's declared RETURN type against the scrutinee
/// (`match_case_field_types`, `core/src/core_check.rs`), which needs
/// metavariables and a per-constructor return-index expression -- this
/// checker has neither (`lang/src/typecheck/whnf.mo`'s header: `Term.hole`
/// is a wildcard, not a solvable meta), and `n + 1 ~ 5` needs arithmetic in
/// unification regardless. Recorded as the remaining gap in
/// `plans/implementations/field-pattern-type-args-not-substituted.md`
/// rather than approximated here.
def rfp_substituted (ind : Inductive) (scrutinee_typ : Term) (rfp : ResolvedFieldPattern) : ResolvedFieldPattern :=
    match rfp {
        mk resolved_name declared_names declared_types written_to_declared =>
            // Annotated local first -- see the matching comment in
            // `resolve_field_pattern_against_constructor`.
            let out : ResolvedFieldPattern := {
                resolved_name := resolved_name,
                declared_names := declared_names,
                declared_types := substitute_inductive_type_params ind scrutinee_typ declared_types,
                written_to_declared := written_to_declared,
            } in
            out,
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
/// `NamePath` -- `InductConstructor.mk`'s `name` is never
/// type-prefixed (see e.g. `arg_types_for_case`'s own doc comment).
/// `List.last` (`init/prelude.mo`) already covers "get the last
/// element"; `Option.none` (an empty `NamePath`) shouldn't happen for
/// a real constructor, handled defensively with an empty-string
/// placeholder rather than assumed impossible.
#[partial]
def constructor_bare_name (np : NamePath) : Identifier :=
    match np {
        NamePath.mk ids =>
            match List.last ids {
                Option.some last_id => last_id,
                Option.none => Identifier.id "",
            },
    }

// `declared_types` below is the constructor's own DECLARED field types,
// expressed over the INDUCTIVE's type parameters (`A`/`B` for `Pair A B`)
// -- deliberately, and only half the answer. `resolve_field_pattern_case`
// instantiates them against the scrutinee's actual type arguments
// (`rfp_substituted`) for both spellings at once, which is why neither this
// function nor `resolve_bare_field_pattern` takes a scrutinee type.
//
// That instantiation used to be missing, and this comment used to record it
// as an unconfirmed gap on the grounds that no corpus failure exercised the
// path with a generic scrutinee. One did:
// `plans/implementations/field-pattern-type-args-not-substituted.md` --
// `p.first` on a `Pair String String` read as `A`, reported wherever an
// expected type was in play and SILENTLY mistyping the binding wherever one
// was not. Rows in `lang/src/module.mo` (`field_pattern_preamble`) and
// `lang/src/tests/infer_tests.mo` (`pair_ind`) hold it closed now.
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
                                else
                                    // Annotated local first -- see the
                                    // matching comment in `type_check`'s
                                    // `Term.hole` arm.
                                    let rfp : ResolvedFieldPattern := {
                                        resolved_name := resolved_name,
                                        declared_names := declared_names,
                                        declared_types := types_from_params params,
                                        written_to_declared := written_to_declared,
                                    } in
                                    ok rfp,
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
            let con_mp : NamePath := NamePath.mk (List.cons case_name List.empty) in
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
def type_check_case_body_checked (name : Identifier) (args : List Identifier) (body : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) (maybe_ind : Option Inductive) : Result TypeError CheckedCase :=
    match type_check body expected_type scope local_types locals {
        ok body_tt =>
            let body_term : Term := body_tt.term in
            let body_typ : Term := body_tt.typ in
            let no_fp : Option FieldPattern := Option.none in
            let resolved_typ_name : Option NamePath := match maybe_ind {
                Option.some ind => Option.some (inductive_type_path ind),
                Option.none => Option.none,
            } in
            let new_case : MatchCase := MatchCase.mk name args body_term no_fp resolved_typ_name in
            // Annotated local first -- see the matching comment in
            // `type_check`'s `Term.hole` arm.
            let cc : CheckedCase := { case_ := new_case, body_typ_ := body_typ } in
            ok cc,
        err e => err e,
    }

/// Type check a variable reference.
///
/// `#[terminating]`: the free-variable path can RE-ENTER the checker on a
/// term it built rather than one taken apart (`try_global_field_access`,
/// `type_check_free_var`'s last fallback -- the non-local field read), so
/// this def is now a member of the checker's mutual-recursion group without
/// a structural descent to show for it. Well-founded all the same: the
/// rebuilt term's subject is the UNDOTTED head, and the recovery refuses
/// anything that does not have a dot to split, so it cannot re-enter itself
/// a second time.
#[terminating]
def type_check_var (idx : I64) (dbg : DebugName) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    if I64.beq idx sentinel then
        type_check_free_var dbg expected_type scope local_types locals
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

/// Split a dotted name string at its FIRST `.` -- the forward-scanning
/// companion to `last_dotted_segment`/`dotted_qualifier` above, which both
/// scan backwards from the end. Field access needs the other split: for
/// `vzero.x` (or `vzero.pos.x`) the SUBJECT is everything before the first
/// dot and the FIELD CHAIN everything after it, in that order.
///
/// `Option.none` when the string has no dot at all -- an undotted name is
/// not a field access, which is why `try_global_field_access` below starts
/// here. `String.slice` takes a LENGTH as its third argument, so the
/// remainder is exactly `len - idx - 1` bytes from `idx + 1`.
#[terminating]
def split_first_dot_go (s : String) (idx : I64) (len : I64) : Option (Pair String String) :=
    if I64.beq idx len then Option.none
    else
        match (String.get s idx : Option U8) {
            Option.some byte_val =>
                if U8.beq byte_val 46u8 then // '.' is ASCII 46
                    Option.some (Pair.pair (String.slice s 0 idx) (String.slice s (idx + 1) (len - idx - 1)))
                else
                    split_first_dot_go s (idx + 1) len,
            Option.none => Option.none
        }

def split_first_dot (s : String) : Option (Pair String String) :=
    split_first_dot_go s 0 (String.length s)

/// Every `.`-separated segment of a dotted name, in written order --
/// `"x"` -> `["x"]`, `"pos.x"` -> `["pos", "x"]`, `"a.b.c"` ->
/// `["a", "b", "c"]`. Head first, so the TAIL is exactly the field chain
/// `field_access_chain` consumes.
///
/// The recursion is on a strictly shorter string (`split_first_dot` peels
/// the head and the dot before recursing) but not on a structural subterm,
/// which is what the termination check looks for -- hence `#[terminating]`
/// rather than a derived proof.
#[terminating]
def dotted_segments (s : String) : List String :=
    match split_first_dot s {
        Option.none => List.cons s List.empty,
        Option.some p =>
            match p {
                Pair.pair head rest => List.cons head (dotted_segments rest),
            },
    }

/// `dotted_segments`' result re-wrapped as `Identifier`s -- hand-rolled
/// rather than `List.map` for the reason `params_all_named`'s own doc
/// comment further down records: a NEW top-level def in this module whose
/// body calls a generic `List.*` op fails at run time with `unresolved
/// global` through the self-hosted evaluator.
#[partial]
def identifiers_of_segments (segs : List String) : List Identifier :=
    match segs {
        List.empty => List.empty,
        List.cons s rest => List.cons (Identifier.id s) (identifiers_of_segments rest),
    }

/// Does `head` name a class? The loose test the class-method path was
/// built on, kept here only to EXCLUDE, never to resolve: a class-qualified
/// name belongs to `class_method_ref`/`resolve_class_method`, so
/// `try_global_field_access` must not reinterpret one as a field lookup.
/// `Map.get` is the case that matters -- `Map` declares no `get`, so the
/// tightened `class_method_ref` refuses it and it arrives at the recovery
/// arm, where the honest answer is `unknown variable 'Map.get'` and not a
/// field of a class.
def dotted_head_names_class (head : String) (scope : Scope) : Bool :=
    match scope_find_class (NamePath.mk (List.cons (Identifier.id head) List.empty)) scope {
        Option.some _ => true,
        Option.none => false,
    }

/// Does `head` name an inductive? A qualified CONSTRUCTOR reference
/// (`List.empty`, `Vec.cons`) reaches the same recovery arm, and it is
/// `type_check_free_var_con`'s to resolve: constructors are registered
/// under their bare name only, so the inductive's own name is exactly the
/// qualifier that must fall through.
def dotted_head_names_inductive (head : String) (scope : Scope) : Bool :=
    match scope_find_inductive (NamePath.mk (List.cons (Identifier.id head) List.empty)) scope {
        ok _ => true,
        err _ => false,
    }

/// The name `try_global_field_access` rebuilds a dotted access's subject
/// under -- `head` as written when it resolves, else the ONE `def_refs` key
/// that ends in `::head`.
///
/// The second half is why this exists. A def's own name is module-qualified
/// by the time CODEGEN elaborates (`qualify_decl_names`, `lang.codegen.
/// qualify`) -- `def vzero` in `simple` is registered as `simple::vzero`,
/// and references are rewritten to match by `resolve_open_alias_term_
/// scoped` -- but that rewriter matches a reference by its WHOLE name text,
/// and a dotted spelling is not one its keys ever carry, so `vzero.x`
/// survives qualification with a bare head. `scope_resolve_name` then misses
/// in the codegen scope while the checker's own (pre-qualification) scope
/// resolves it, which is exactly the shape of a fix that passes `monad
/// check` and fails `monad compile` -- measured on the Gap 3 fixture:
/// `elaborate_class: 3 decl(s) did not elaborate (kept un-elaborated):
/// prelude::Lens, simple::vzero_x, simple::vzero_y`, each with `unknown
/// variable 'vzero.x'`.
///
/// The key is returned as the rebuilt subject's NAME, not just used as a
/// presence test, because `def_symbol_name` is the name VERBATIM
/// (`lang/codegen/symbols.mo`): rebuilding the subject as the bare `vzero`
/// inside a qualified graph would resolve in the checker and then reach
/// codegen as a symbol nothing defines -- the same failure one stage later.
///
/// A suffix with more than one match is ambiguous and returns `Option.none`,
/// i.e. the honest `unknown variable`: two modules declaring the same bare
/// name is precisely what qualification exists to keep apart, and the
/// rewriter above (which resolves that case by the importing module's own
/// `use`/`open`) is the only place with the information to choose.
///
/// The miss half consults `ScopeData.bare_aliases` (noted at
/// registration) rather than scanning every `def_refs` key per miss --
/// same unique-owner rule, one O(1) lookup.
#[partial]
def resolve_dotted_head (head : String) (scope : Scope) (locals : LocalScope) : Option String :=
    match scope_resolve_name (NameRef.nid (Identifier.id head)) scope locals {
        ok _ => Option.some head,
        err _ =>
            let g : ScopeData := scope_globals scope in
            match bare_map_lookup head g.bare_aliases {
                Option.some keys =>
                    match keys {
                        List.cons k rest =>
                            match rest {
                                List.empty => Option.some k,
                                List.cons _ _ => Option.none,
                            },
                        List.empty => Option.none,
                    },
                Option.none => Option.none,
            },
    }

/// Gap 3 recovery: a dotted name whose SUBJECT is a top-level def rather
/// than a local binder.
///
/// `lower_path_ids` (`lang/src/parser/lower_parse.mo`) settles the
/// "module-qualified global, or field access?" ambiguity on exactly one
/// question -- is the path's first segment a local binder? -- because the
/// parser has no scope to ask. A local subject (`p.first`) is therefore
/// already a `FieldPattern` match by the time the checker sees it; a
/// top-level one (`vzero.x`) is not, and the whole dotted spelling
/// survives as ONE global name, which no def is registered under -- so the
/// checker reported `unknown variable 'vzero.x'` for the entirely ordinary
/// pair `pub def vzero : Vec3` and `vzero.x`.
///
/// Nothing about struct layout or LLVM types ever blocked the non-local
/// case; only the missing desugaring did. This rebuilds the access with the
/// SAME builder the parser uses (`field_access_chain`, now in `lib::types`)
/// and re-enters `type_check` on it -- one desugaring, two callers, so the
/// two cannot drift apart.
///
/// Re-entering the checker, rather than resolving the field's type here, is
/// also what carries the fix to CODEGEN: `elaborate_def_with_scope`
/// (`lang/module.mo`) writes the checker's rewritten term back into the
/// `Def`, and both `elaborate_module_decls` and its best-effort sibling go
/// through it -- so the field-pattern match codegen needs is in the `Def`
/// with no second pass.
///
/// The rebuilt scrutinee is the UNDOTTED head, so the recursion terminates
/// at once: `type_check` on `Term.var sentinel (named head)` takes the
/// ordinary global path. `#[partial]` because that recursion is not
/// structural -- the term handed back to `type_check` is built here, not
/// taken apart from the one that arrived.
///
/// `Option.none` means "not this case", and the caller falls through to the
/// constructor path unchanged. Four gates, in order:
///
///   * no dot at all -- not a field access;
///   * the head names a CLASS -- the class-method path's business;
///   * the head names an INDUCTIVE -- the constructor path's, which
///     `type_check_free_var_con` owns (`List.empty`);
///   * the head resolves to nothing, even after `resolve_dotted_head`'s
///     module-qualified fallback -- a genuine `unknown variable`, which the
///     caller must still report as one.
#[partial]
def try_global_field_access (id : Identifier) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Option (Result TypeError TypedTerm) :=
    match id {
        Identifier.id s =>
            match dotted_segments s {
                List.empty => Option.none,
                List.cons head rest =>
                    match rest {
                        List.empty => Option.none,
                        List.cons _ _ =>
                            if dotted_head_names_class head scope then Option.none
                            else if dotted_head_names_inductive head scope then Option.none
                            else
                                match resolve_dotted_head head scope locals {
                                    Option.none => Option.none,
                                    Option.some subject =>
                                        let head_id : Identifier := Identifier.id subject in
                                        let fields : List Identifier := identifiers_of_segments rest in
                                        let scrutinee : Term := Term.var sentinel (DebugName.named head_id) in
                                        Option.some (type_check (field_access_chain scrutinee fields) expected_type scope local_types locals),
                                },
                    },
            },
    }

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
    let con_mp : NamePath := NamePath.mk (List.cons bare_name List.empty) in
    match scope_find_inductive_by_constructor con_mp scope {
        Option.some ind =>
            match find_constructor_in_inductive ind con_mp {
                Option.some _ => ok (mk_typed (Term.var sentinel dbg) (con_ref_result_type id expected_type scope)),
                Option.none => err (TypeError.unknown_var (NameRef.nid id)),
            },
        Option.none => err (TypeError.unknown_var (NameRef.nid id)),
    }

/// A constructor REFERENCE's own result type, for the INFER case --
/// `type_check_free_var_con`'s counterpart to `con_result_type`.
///
/// This is the path a real source program actually takes: the parser
/// never builds `Term.con` (see `type_check_con`'s own doc comment), so
/// `Slim.mk 1` is an application whose head is the FREE VARIABLE
/// "Slim.mk", resolved here. Returning `expected_type` verbatim meant
/// that in infer mode a constructor application had no inferred type,
/// which propagated into every `let`-bound scrutinee (both `let ... in`
/// and the do-block form, which desugar to `Term.app (Term.lam x hole
/// ...) value`): `type_check_app_ordinary` builds its Pi from the
/// ARGUMENT's inferred type, `type_check_lam`'s `if is_hole t then
/// arg_typ else t` then had two holes to choose between, so the local's
/// type stayed hole and `find_inductive_for_cases` fell all the way
/// through to the ambiguous constructor-name scan. On a bare name two
/// inductives share (every `mk`), that scan correctly errors -- and
/// under codegen's best-effort elaboration (`elaborate_module_decls_
/// best_effort`, lang/module.mo, which by design leaves a failing decl
/// unchanged) the arms' binders were left untyped, so `+` stayed a
/// GENERIC class call whose dictionary (`Add_A_add` -> `__Dict_Add_A`
/// -> `Add_A_add_closure_shim` -> `Add_A_add`) recursed until the stack
/// died. Confirmed live as a SIGSEGV in `Add_A_add`'s prologue
/// `movaps`, on a program whose IR was otherwise correct, and by
/// bisection: the identical program with the constructors RENAMED apart
/// specialized to `Add_I64_add` and ran fine.
///
/// Only fires when the reference is written QUALIFIED ("Slim.mk"), and
/// only when that qualifier names a real inductive owning this
/// constructor -- so the type is read off the name the source actually
/// wrote, never guessed from an ambiguous bare-name scan
/// (`scope_find_inductive_by_constructor` is first-match, which is
/// exactly what must not be trusted here). A bare reference, an
/// unrecognized qualifier, or a real ambient `expected_type` all keep
/// today's behavior untouched, so this only ever ADDS precision --
/// `find_inductive_for_cases`'s own "only ever add a strictly-better
/// preferred path" discipline.
def con_ref_result_type (id : Identifier) (expected_type : Term) (scope : Scope) : Term :=
    // A PARAMETERIZED inductive's bare name is not a complete type
    // (`List.cons 1 rest` is `List I64`, not `List`) -- see
    // `inductive_has_params`; leave those to the existing hole fallback.
    if con_ref_wants_inference expected_type
    then
        match id {
            Identifier.id s =>
                match dotted_qualifier s {
                    Option.some qual =>
                        let qual_mp : NamePath := NamePath.mk (List.cons (Identifier.id qual) List.empty) in
                        match scope_find_inductive qual_mp scope {
                            // The params check must be on the inductive
                            // actually being NAMED (`qual_ind`, from the
                            // written qualifier), not on `ind` -- `ind`
                            // comes from a first-match bare-name scan
                            // (`scope_find_inductive_by_constructor`) and
                            // is a DIFFERENT inductive whenever two types
                            // share a constructor name, which is the whole
                            // scenario this path exists for.
                            ok qual_ind =>
                                con_owner_type qual_ind (NamePath.mk (List.cons (Identifier.id (last_dotted_segment s)) List.empty)) expected_type,
                            err _ => expected_type,
                        },
                    Option.none => bare_con_ref_result_type s expected_type scope,
                },
        }
    else expected_type

/// The type a constructor reference has before any argument is applied:
/// the owning inductive when it is ground; `T _ _` for a NULLARY
/// constructor of a parameterized one (`BTreeMap.empty`), so a class call
/// can still read its carrier off the argument; otherwise `fallback`.
def con_owner_type (ind : Inductive) (con_mp : NamePath) (fallback : Term) : Term :=
    match ind {
        Inductive.mk _ params _ _ _ _ =>
            let head : Term := Term.var sentinel (DebugName.named (inductive_bare_name ind)) in
            match params {
                List.empty => head,
                List.cons _ _ =>
                    match find_constructor_in_inductive ind con_mp {
                        Option.none => fallback,
                        Option.some ctor =>
                            match ctor {
                                InductConstructor.mk _ fields _ =>
                                    match fields {
                                        List.empty => apply_holes head params,
                                        List.cons _ _ => fallback,
                                    },
                            },
                    },
            },
    }

#[partial]
def apply_holes (head : Term) (params : List Param) : Term :=
    match params {
        List.empty => head,
        List.cons _ rest => apply_holes (Term.app head Term.hole) rest,
    }

/// A bare constructor (`true` after `open Bool`) names its type only when
/// exactly one ground inductive owns it.
def bare_con_ref_result_type (name : String) (expected_type : Term) (scope : Scope) : Term :=
    match scope_find_all_inductives_by_constructor (NamePath.mk (List.cons (Identifier.id name) List.empty)) scope {
        List.empty => expected_type,
        List.cons only rest =>
            match rest {
                List.cons _ _ => expected_type,
                List.empty =>
                    con_owner_type only (NamePath.mk (List.cons (Identifier.id name) List.empty)) expected_type,
            },
    }

/// Whether a constructor reference's ambient expected type carries no
/// real information about its RESULT, so inferring the owning inductive
/// is strictly better than echoing it back.
///
/// A bare `Term.hole` is the obvious case. The subtler one is the shape
/// `type_check_app_ordinary` synthesizes for a call's callee --
/// `Term.pi <arg type> <the call's own expected type>` -- which is NOT a
/// hole even when the call itself is being inferred, because only its
/// RETURN is. A constructor reference checked against that Pi used to
/// echo the Pi straight back, `extract_pi_ret` then returned its hole
/// return, and the application came out untyped after all: `Slim.mk`
/// alone inferred as `Slim` while `Slim.mk 1` inferred as a hole.
/// Looking through the Pi to its return is what makes the FIX actually
/// reach applied constructors, which is the only form that matters here
/// (a `let` binds `Slim.mk 1`, never the bare reference).
///
/// Nested pis are walked to the final return for the multi-argument
/// case (`Wide.mk 10 20 30` builds one Pi layer per argument).
#[terminating]
def con_ref_wants_inference (expected_type : Term) : Bool :=
    match expected_type {
        Term.hole => true,
        // Guarded for the reason the two above record: a
        // quantifier-headed expectation used to answer the catch-all
        // `false` here, and the fold would otherwise walk into the
        // quantifier's body looking for a hole.
        Term.pi b _ ret =>
            if binder_is_explicit b then con_ref_wants_inference ret else false,
        _ => false,
    }

/// Whether an inductive declares type PARAMETERS (`List A`, `Option A`,
/// `Result E T`) as opposed to being a ground type (`Slim`, `Term`,
/// `Identifier`).
///
/// `qualified_con_ref_typ` names an inductive by its bare name alone,
/// which is only a complete type for a ground one: for `List` the real
/// type of `List.cons 1 rest` is `List I64`, and answering the
/// unapplied `List` produces a "type mismatch: expected (List A), found
/// List" the moment it meets a real signature (confirmed live against
/// `init/prelude.mo`'s own `List.append`). Reconstructing the applied
/// form would mean solving the parameters from the arguments -- exactly
/// the job `scope_find_def_sig`'s registered signatures already do for
/// everything that has one -- so a parameterized inductive is simply
/// left to the existing hole fallback, unchanged. The collision hazard
/// this whole fix targets is ground-type constructors (`mk` on two
/// different record-shaped types), which is precisely the case kept.
def inductive_has_params (ind : Inductive) : Bool :=
    match ind {
        Inductive.mk _ params _ _ _ _ =>
            match params {
                List.empty => false,
                List.cons _ _ => true,
            },
    }

/// The type for a resolved-but-signature-less free variable: its owning
/// inductive when the reference is a QUALIFIED constructor
/// (`Slim.mk` -> `Slim`), else the `sig` hole this always returned.
///
/// Only fires when the qualifier names a real inductive that really
/// declares this constructor, so the answer comes from the name the
/// source wrote rather than an ambiguous bare-name scan -- and only when
/// `sig` carries nothing (a registered def signature always wins). Purely
/// additive: every other reference keeps the exact hole it had.
/// See `con_ref_result_type` for the failure this closes.
def qualified_con_ref_typ (dbg : DebugName) (sig : Term) (scope : Scope) : Term :=
    if is_hole sig
    then
        match dbg {
            DebugName.named id =>
                match id {
                    Identifier.id s =>
                        match dotted_qualifier s {
                            Option.some qual =>
                                let qual_mp : NamePath := NamePath.mk (List.cons (Identifier.id qual) List.empty) in
                                let bare_mp : NamePath := NamePath.mk (List.cons (Identifier.id (last_dotted_segment s)) List.empty) in
                                match scope_find_inductive qual_mp scope {
                                    ok qual_ind =>
                                        match find_constructor_in_inductive qual_ind bare_mp {
                                            Option.some _ => con_owner_type qual_ind bare_mp sig,
                                            Option.none => sig,
                                        },
                                    err _ => sig,
                                },
                            Option.none => bare_con_ref_result_type s sig scope,
                        },
                },
            DebugName.unnamed => sig,
        }
    else sig

/// Whether an unresolved reference is eligible for the CLASS-METHOD
/// lookup below: a reference written with a dotted qualifier
/// (`Foldable.foldr`) is one only when that qualifier really names a
/// class; an undotted one (a bare method name, which the very same
/// bare-name lookup below is what resolves) keeps today's behavior.
///
/// Class methods are registered under their BARE method name
/// (`add_methods_go`, `lang/scope.mo`), so `scope_find_class_def_by_name`
/// matches on that bare name -- which is exactly why the lookup strips
/// the qualifier first. Stripping it UNCONDITIONALLY is what makes a
/// qualified CONSTRUCTOR reference match whichever class happens to
/// declare a method of the same bare name: `List.empty`, whose qualifier
/// is the INDUCTIVE `List`, matches class `FromListLiteral`'s own `empty`
/// method, whose promoted def for `init/prelude.mo`'s `instance
/// FromListLiteral List` is `FromListLiteral_List_empty` -- the very def
/// whose body the reference appears in. Resolving it "successfully"
/// rewrites that body into its own name, a strict self-reference the
/// evaluator reports as `ce_cycle` (measured: with the applied-head arm
/// in `lang/scope.mo`'s `term_matches_carrier` -- the carrier the wrong
/// resolution needs to succeed at all -- but without this guard, the
/// self-hosted meta-evaluator died with `ce_cycle 3`, which is what kept
/// that arm out of P5). The qualifier is the only
/// thing that tells the two kinds of reference apart, so it is required
/// to name a class; a qualifier naming an INDUCTIVE falls through to
/// `type_check_free_var_con`, the constructor path, which is what
/// `List.empty`/`Option.some`/`Bool.true` mean.
def ref_names_class_method (id : Identifier) (scope : Scope) : Bool :=
    match id {
        Identifier.id s =>
            match dotted_qualifier s {
                // No dot at all: this is not a QUALIFIED reference, and the
                // arm below is deliberately loose for it -- the caller scans
                // every class for the bare name. Tightening that (a method
                // name declared in two classes can still resolve against the
                // wrong one) is a separate piece of work, not this
                // predicate's.
                Option.none => true,
                // Qualified: decided by `class_method_ref`, the SAME
                // predicate the resolver itself uses (`lang/scope.mo`), and
                // that is the point of delegating rather than repeating the
                // test -- a second, independently-written membership rule is
                // exactly how the two sides drifted apart in the first
                // place. `Map.get` fails here now (no `get` among `Map`'s
                // declared methods), so it falls through to
                // `type_check_free_var_con` and reports `unknown variable
                // 'Map.get'` instead of silently matching `MonadState.get`'s
                // bare name in some unrelated class.
                Option.some _ =>
                    match class_method_ref (scope_data_classes (scope_globals scope)) id {
                        Option.some _ => true,
                        Option.none => false,
                    },
            },
    }

/// Look up a free variable by debug name in the scope.
///
/// `local_types` is threaded through for exactly one reason: the last
/// fallback can rebuild the reference as a field-access chain and re-enter
/// `type_check` on it (`try_global_field_access` below), and `type_check`
/// needs the full local context to do that. Nothing else here reads it.
/// The declared-signature fallback of `type_check_free_var`'s resolved
/// arm: the def's REAL registered signature (`ScopeData.def_sigs` --
/// `ScopeDef.sig` itself is unconditionally `Term.hole` by its own
/// load-bearing design, `build_scope_def`, `lang/scope.mo`), or the
/// constructor-recovery path for a name that resolved but has none
/// registered. Returned via `type_check_app`'s signature-driven path,
/// checking arguments against real parameter types and solving the
/// signature's type variables (V in `def get_first {V : Type} (xs : List
/// V) : Option V`) from the arguments' actual types -- without it, EVERY
/// call result types as `Term.hole` and match arms on it bind the
/// constructor's raw skolemized parameter ("type mismatch: expected A,
/// found I64"), nested matches on those can't disambiguate a bare
/// `mk`/`empty` constructor ("ambiguous constructor"), `{ .. }` struct
/// patterns can't resolve ("the matched value's type isn't known"), and
/// struct literals passed as call arguments get no expected type
/// ("cannot infer struct type"). One root cause, ~70 sites in the
/// compiler's own closure.
///
/// The `Option.none` half: no registered signature. For an ordinary def
/// that means the `sig`-hole fallback; but a CONSTRUCTOR reference
/// resolves in `type_check_free_var` too (constructors ARE registered
/// names), and for one written qualified -- `Slim.mk` -- the qualifier
/// names its owning inductive exactly. Recovering that is what gives a
/// `let`-bound constructor value a real type; see `con_ref_result_type`
/// for why the hole was load-bearing in the worst way (an untyped
/// scrutinee sent `find_inductive_for_cases` into its ambiguous
/// bare-name scan, which under codegen's best-effort elaboration left `+`
/// generic and its dictionary recursing until the stack died).
/// `type_check_free_var_con` does the same job for a name that DOESN'T
/// resolve -- this is the same fix on the path a real qualified
/// constructor reference actually takes.
def free_var_declared_typ (resolved_name : NamePath) (sig : Term) (dbg : DebugName) (scope : Scope) : Term :=
    match scope_find_def_sig resolved_name scope {
        Option.some real_sig => real_sig,
        Option.none => qualified_con_ref_typ dbg sig scope,
    }

/// A free variable's def lookup with item-5.1's bare-vs-qualified
/// tolerance: the exact name first, then -- only on a miss, and only
/// when the bare-name side table (`ScopeData.bare_aliases`, noted at
/// registration) holds exactly one qualified owner -- the qualified
/// spelling under which the whole-program scope actually registered
/// it. Type/struct/class declarations are renamed by qualification
/// (`qualify_one_decl_name`) while the rewriter deliberately leaves
/// type annotations source-spelled, so a bare annotation head
/// (`fn (p : Pair String Toml.Value) => ...`, checked as a term by
/// `type_check_lam_inferring`) reaches here bare after the exact-only
/// lookup misses. The unique-owner rule is the same ambiguity policy
/// `resolve_dotted_head` and `scope_find_inductive`'s fallback already
/// apply: two owners means a genuine miss, not a guess. The consult is
/// a map lookup, not the per-miss `def_refs` key scan this originally
/// was -- `def_refs` holds thousands of keys and a bare miss is the
/// common case post-qualification, so the scan was a measured ~20x
/// blowup of `elaborate_module_decls`.
def resolve_free_var_def (id : Identifier) (scope : Scope) (locals : LocalScope) : Result ScopeError ScopeDef :=
    let exact : Result ScopeError ScopeDef := scope_resolve_name (NameRef.nid id) scope locals in
    match exact {
        ok sd => ok sd,
        err _ =>
            let g : ScopeData := scope_globals scope in
            let bare : String := match id { Identifier.id s => s } in
            match bare_map_lookup bare g.bare_aliases {
                Option.some keys =>
                    match keys {
                        List.cons k rest =>
                            match rest {
                                List.empty => scope_resolve_name (NameRef.nid (Identifier.id k)) scope locals,
                                List.cons _ _ => exact,
                            },
                        List.empty => exact,
                    },
                Option.none => exact,
            },
    }

def type_check_free_var (dbg : DebugName) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match dbg {
        DebugName.named id =>
            let nref : NameRef := NameRef.nid id in
            let result : Result ScopeError ScopeDef := resolve_free_var_def id scope locals in
            match result {
                ok sd => match sd {
                    mk resolved_name _ sig _ _ =>
                        match scope_find_cubical_prim resolved_name scope {
                            // A cubical primitive bound by `#[cubical "..."]`
                            // (the `with Cubical` block in
                            // `init/src/prelude.mo`) referenced BARE. For
                            // an arity-0 primitive (`I`, `i0`, `i1`) the
                            // reference IS the term: rewrite it to the
                            // `Term.cubical` it stands for, typed by the
                            // primitive's own rule (`cubical_result_type`).
                            // A parameterized primitive referenced bare
                            // (`ineg` as a value, `imeet` partially applied)
                            // takes the declared-signature path -- its
                            // body-less declaration still registered a real
                            // `def_sigs` entry, and that signature is the
                            // right type for the under-applied case. A
                            // SATURATED application never reaches here:
                            // `type_check_app`'s cubical probe runs first,
                            // ahead of its def-call probe, precisely so the
                            // declared signature cannot type the call and
                            // leave the rewrite never happening.
                            Option.some prim =>
                                if I64.beq (cubical_arity prim) 0 then
                                    ok (mk_typed (cub prim List.empty) (cubical_result_type prim))
                                else
                                    ok (mk_typed (Term.var sentinel dbg)
                                        (free_var_declared_typ resolved_name sig dbg scope)),
                            Option.none =>
                                // A LOCAL of this name shadows any
                                // global: its own type is not a def
                                // signature, so never reify it from
                                // one (the same guard the app-spine and
                                // constructor probes apply).
                                if is_some_local (scope_find_local id locals)
                                then ok (mk_typed (Term.var sentinel dbg)
                                    (free_var_declared_typ resolved_name sig dbg scope))
                                else
                                    reify_bare_constrained_ref resolved_name
                                        (free_var_declared_typ resolved_name sig dbg scope)
                                        expected_type scope locals dbg,
                        },
                },
                err _ =>
                    // A qualified class-method reference (`Foldable.foldr`)
                    // is stored under its bare method name only
                    // (`add_methods_go`) -- strip to the last dotted
                    // segment before looking it up, mirroring
                    // `type_check_free_var_con`'s identical existing fix
                    // just below for qualified constructor references.
                    // Only a reference that really IS a class-method
                    // reference gets that far (`ref_names_class_method`)
                    // -- otherwise a qualified CONSTRUCTOR reference
                    // (`List.empty`) matches an unrelated class's
                    // same-named method and resolves to a promoted def
                    // standing inside its own body, see that function's
                    // doc comment.
                    let bare_id : Identifier := match id { Identifier.id s => Identifier.id (last_dotted_segment s) } in
                    let clsd_result : Result ScopeError ScopeClassDef :=
                        if ref_names_class_method id scope
                        then scope_find_class_def_for_ref id bare_id scope
                        else err (ScopeError.class_not_found (NamePath.mk (List.cons bare_id List.empty))) in
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
                            // Not a class method. Before falling back to the
                            // constructor path, try the field-access recovery
                            // -- a dotted name whose SUBJECT is a top-level
                            // def (`vzero.x`) is an ordinary field read the
                            // parser could not desugar, because it settles
                            // the local-vs-global ambiguity on local binders
                            // only. See `try_global_field_access`'s own doc
                            // comment; it refuses every case that belongs to
                            // either path above, so a `List.empty` still
                            // reaches `type_check_free_var_con` and a
                            // `Map.get` still reports `unknown variable`.
                            match try_global_field_access id expected_type scope local_types locals {
                                Option.some tt_result => tt_result,
                                Option.none => type_check_free_var_con id expected_type dbg scope,
                            },
                    },
            },
        DebugName.unnamed =>
            ok (mk_typed (Term.var sentinel dbg) (Term.sort (SortLevel.concrete 1))),
    }

/// Look up a bound variable by de Bruijn index.
def type_check_bound_var (idx : I64) (dbg : DebugName) (local_types : List Term) : Result TypeError TypedTerm :=
    match nth_type idx local_types {
        Option.some typ =>
            ok (mk_typed (Term.var idx dbg) (term_shift (idx + 1) typ)),
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
///
/// `#[terminating]` for the same reason as `names_of_decls_go`
/// (`lang/src/elaborate.mo`): the `type_check` cycle terminates on the
/// structure of the TERM being checked, not on any one parameter
/// position, and the lexical decrease check cannot see across a mutual
/// edge. Every other member of the cycle happens to pass it -- their
/// in-cycle calls sit in match-scrutinee position, which the check does
/// not judge -- but Stage 2's lambda dispatch calls cycle members as
/// plain tail calls (`check_path_lam`, `type_check_lam_inferring`), and
/// those are judged. The recursion is well-founded (each descends into
/// a strict subterm of the lambda being checked); it is just not
/// structurally measurable, so it is asserted here rather than gamed
/// into scrutinee position.
/// R2c: the parameter is the lambda's own `Binder`, not a bare `DebugName`
/// -- mirroring `type_check_pi`, which has taken a `Binder` since R2a. A
/// name is only needed where a local is bound, and `binder_name` peels it
/// there.
#[terminating]
def type_check_lam (bnd : Binder) (t : Term) (body : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match expected_type {
        // An explicit binder is a real function type, so the lambda is
        // checked against it. Anything else (`BinderInfo.binder` -- a
        // quantified type variable, yesterday's `forall`, and
        // `BinderInfo.level`) has no argument to check against: the first
        // arm below is skipped and the chain is stripped instead.
        Term.pi b _ _ =>
            if binder_is_explicit b
            then type_check_lam_explicit bnd t body expected_type scope local_types locals
            else type_check_lam_strip bnd t body expected_type scope local_types locals,
        // Stage 2: a path ABSTRACTION. `fn i => body` checked against a
        // `PathP A a b` binds the binder at the interval, checks the body
        // against the line applied to the fresh dimension, and requires
        // the body's two boundaries to match the type's endpoints --
        // `body[i:=i0] ≡ a`, `body[i:=i1] ≡ b`. Matched BEFORE the
        // inferring arm below because that arm discards the expected
        // type, and the boundary is the whole content of this rule.
        Term.cubical _c => check_path_lam bnd t body expected_type scope local_types locals,
        // An expected type SPELLED as a def reference -- `Path A a b`,
        // whose own body is a `PathP` -- never reaches the arm above,
        // because that dispatch is syntactic. Reduce the head and use the
        // path rule on the reduced form when it lands on a cubical type;
        // every other result is handled exactly as before, so this only
        // ever accepts more. `whnf` is what makes the reduced form a
        // `Term.cubical` at all (`as_cubical_type`, `lang/typecheck/
        // whnf.mo`): delta turns `Path A a b` into an application SPINE of
        // the `pathp` primitive's name, which no path rule recognizes.
        // Without this a path abstraction checked against the library
        // `Path` alias infers a Pi instead and is rejected (measured:
        // `refl : Path A a a := fn (i : Cubical.I) => a` failed with
        // "expected (Path A a a), found (I -> A)" -- see univalence.md's
        // Stage 2 note).
        _ =>
            let reduced : Term := whnf scope locals expected_type in
            match reduced {
                Term.cubical _c => check_path_lam bnd t body reduced scope local_types locals,
                _ => type_check_lam_inferring bnd t body scope local_types locals,
            },
    }

/// The explicit-arrow arm of `type_check_lam`. Split out so the merged
/// `Term.pi` arm above can dispatch on the binder without re-indenting the
/// whole rule.
#[terminating]
def type_check_lam_explicit (bnd : Binder) (t : Term) (body : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match expected_type {
        Term.pi _b arg_typ ret_typ =>
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
            // collision -- confirmed via cli/src/main.mo's own `main`, see
            // plans/bootstrapping/self-hosted-compiler.md's changelog).
            let bound_typ : Term := if is_hole t then arg_typ else t in
            let extended_types : List Term := List.cons bound_typ local_types in
            let lv : LocalVar := {
                name := debug_name_to_id (binder_name bnd),
                typ := bound_typ,
                multiplicity := Multiplicity.many,
            } in
            let extended_locals : LocalScope := scope_push_local lv locals in
            match type_check body ret_typ scope extended_types extended_locals {
                ok body_tt =>
                    let checked_body : Term := body_tt.term in
                    let body_typ : Term := body_tt.typ in
                    let lam_term : Term := Term.lam bnd bound_typ checked_body in
                    // The ambient Pi wins whenever its RETURN carries
                    // real information -- that is the bidirectional
                    // precision this arm exists for, and it is
                    // unchanged. Its return being an uninformative
                    // hole is the other case, and echoing the whole Pi
                    // back verbatim then discarded the body type just
                    // inferred: `(e : T)` desugars (`paren_try_ann`,
                    // `lang/parser.mo`) to exactly this applied-lambda
                    // shape, so `IO.pure (List.empty : List I64)` typed
                    // its ARGUMENT as a hole, `solve_typevars` had
                    // nothing to solve `A` from, and the whole call
                    // came out the unsolved `IO A` -- reported one
                    // level up as "type mismatch: expected (IO A),
                    // found (IO (List I64))" the moment a match arm
                    // unified it. Prefer the inferred Pi there.
                    let lam_typ : Term :=
                        if is_hole ret_typ then Term.pi binder_anon bound_typ body_typ else expected_type in
                    // The body's own type against the arrow's codomain.
                    // `lam_typ` above is the declared Pi ECHOED back, so
                    // the def-boundary check cannot see this half at all:
                    // without it `def p (x : I64) : I64 := "hello"`
                    // checks cleanly. `body_type_error` is the same
                    // comparison, and the same guards, that
                    // `lang/module.mo`'s `body_signature_diagnostics` runs
                    // at the def boundary.
                    //
                    // SKIPPED when the arrow PROMISES a function and the
                    // body did not infer one. That is not laziness: a def
                    // whose first parameter is a DESTRUCTURING pattern
                    // (`def f ({a, b, ..} : P) (x : T) : R := ...`) gets a
                    // Pi chain that is longer than its lam chain, because
                    // the remaining parameters become bindings INSIDE the
                    // body -- so the body's type is the innermost result
                    // and the codomain is still a Pi. Measured: `lang/src/
                    // module.mo`'s `locals_with_class_typevars`,
                    // `locals_with_inductive_params` and
                    // `elaborate_def_with_scope` all reject without this.
                    // The other direction -- a Pi inferred where a
                    // non-function was expected, or two non-Pi types that
                    // disagree -- is still compared, which is what catches
                    // `def p (x : I64) : I64 := "hello"`.
                    if is_pi_typ ret_typ && Bool.not (is_pi_typ body_typ)
                    then ok (mk_typed lam_term lam_typ)
                    else match body_type_error body body_typ ret_typ scope locals {
                        Option.none => ok (mk_typed lam_term lam_typ),
                        Option.some e => err e,
                    },
                err e => err e,
            },
        _ => err (TypeError.custom "type_check_lam_explicit: expected a function type"),
    }

/// The non-explicit arm of `type_check_lam`: a quantified-type-variable or
/// level binder is the SAME lambda check with the binder stripped, exactly
/// as `unify_go` strips one before comparing. Without this arm such an
/// expected type fell to the inferring arm and was discarded outright, so
/// EVERY polymorphic def's body -- and every monomorphic def whose declared
/// type got over-generalized -- was checked against `Term.hole`, i.e. not
/// checked. Stripping is sound here because a reference to the binder
/// inside the body is a free `sentinel` var resolved BY NAME (the def's
/// type variables are skolemized into `locals` by
/// `locals_with_def_typevars`, `lang/module.mo`), not a de Bruijn index
/// into this binder -- so removing the binder renumbers nothing.
#[terminating]
def type_check_lam_strip (bnd : Binder) (t : Term) (body : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match expected_type {
        Term.pi _b _dom cod => type_check_lam bnd t body cod scope local_types locals,
        _ => err (TypeError.custom "type_check_lam_strip: expected a binder"),
    }

/// The inferring arm of `type_check_lam`, factored out so the path
/// arm above can fall back to it verbatim instead of duplicating the
/// body. No expected type to check against: the binder's type is the
/// written annotation (checked on its own), and the result is the Pi
/// built from it and the body's inferred type.
def type_check_lam_inferring (bnd : Binder) (t : Term) (body : Term) (scope : Scope)
    (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match type_check t Term.hole scope local_types locals {
        ok t_tt =>
            let inferred_typ : Term := t_tt.typ in
            let extended_types : List Term := List.cons t local_types in
            let lv : LocalVar := {
                name := debug_name_to_id (binder_name bnd),
                typ := t,
                multiplicity := Multiplicity.many,
            } in
            let extended_locals : LocalScope := scope_push_local lv locals in
            match type_check body Term.hole scope extended_types extended_locals {
                ok body_tt =>
                    let checked_body : Term := body_tt.term in
                    let body_typ : Term := body_tt.typ in
                    let pi_typ : Term := Term.pi binder_anon t body_typ in
                    let lam_term : Term := Term.lam bnd t checked_body in
                    ok (mk_typed lam_term pi_typ),
                err e => err e,
            },
        err e => err e,
    }

/// The path-abstraction half of the Stage 2 rules: `fn i => body`
/// against `PathP A a b`. The binder is a DIMENSION -- `I` when the
/// annotation is a hole, and a written annotation must check AS the
/// bare interval (the CHECKED term is compared because a source
/// annotation lowers to a bare name reference that only becomes the
/// cubical term inside `type_check`).
///
/// The body's expected type is the line applied to the fresh dimension:
/// `A i`. The line lives OUTSIDE the new binder, so it shifts up one
/// before the application; the dimension is de Bruijn 0 under it.
///
/// The result echoes the expected `PathP` back: unlike the Pi arm there
/// is no return type to rebuild, and unlike the inferring arm the
/// expected type here is the one thing the boundary rule was checked
/// against. PathP stays rigid -- a body-less declaration never enters
/// `def_bodies` (P1), so the `Term.pi` arm above can never win over this
/// one by delta.
///
/// `parts` is peeled here rather than passed in: the dispatch in
/// `type_check_lam` knows only that the expected type is cubical, and
/// this rule -- not the caller -- decides what shape of cubical type
/// makes a path binder.
///
/// `#[terminating]` for the same reason `type_check_lam` above carries
/// it: the non-PathP fallback tail-calls `type_check_lam_inferring`, a
/// member of the `type_check` cycle, and that call has no lexical
/// decrease to show. The recursion it feeds descends into a strict
/// subterm of the lambda being checked.
#[terminating]
def check_path_lam (bnd : Binder) (t : Term) (body : Term) (expected_type : Term)
    (scope : Scope) (local_types : List Term) (locals : LocalScope)
    : Result TypeError TypedTerm :=
    match path_parts_of expected_type {
        // A cubical expected type that is not a saturated PathP is not a
        // binder shape; the same inferring fallback as `type_check_lam`'s
        // `_` arm is the honest answer for it.
        Option.none => type_check_lam_inferring bnd t body scope local_types locals,
        Option.some parts =>
            match type_check t Term.hole scope local_types locals {
                err e => err e,
                ok t_tt =>
                    match Bool.or (is_hole t) (peels_to_bare_interval t_tt.term) {
                        false => err (TypeError.custom
                            "a path abstraction's binder is a dimension: its type must be the interval"),
                        true =>
                            let binder_typ : Term := cub_interval in
                            let extended_types : List Term := List.cons binder_typ local_types in
                            let lv : LocalVar := {
                                name := debug_name_to_id (binder_name bnd),
                                typ := binder_typ,
                                multiplicity := Multiplicity.many,
                            } in
                            let extended_locals : LocalScope := scope_push_local lv locals in
                            let body_expected : Term :=
                                Term.app (term_shift 1 parts.line) (Term.var 0 (binder_name bnd)) in
                            match type_check body body_expected scope extended_types extended_locals {
                                err e => err e,
                                ok body_tt =>
                                    match check_path_boundary body_tt.term parts scope local_types locals {
                                        err e => err e,
                                        ok _ =>
                                            let lam_term : Term := Term.lam bnd binder_typ body_tt.term in
                                            ok (mk_typed lam_term expected_type),
                                    },
                            },
                    },
            },
    }

/// The boundary rule of the path abstraction: `body[i:=i0] ≡ a` and
/// `body[i:=i1] ≡ b`, the one-binder substitution removing the dimension
/// so both sides compare at the outer level the endpoints live at.
///
/// The substituted body is first put through `normalize_path_boundary`:
/// a body like `fn i => p (ineg i)` lands on `p (ineg i0)`, and while
/// `whnf` folds the DIMENSION (`ineg i0` to `i1`), the application
/// `p i1` itself is stuck -- `whnf_go`'s app arm needs a `Term.lam`
/// head -- and the comparison would fail against the endpoint for a
/// rule this module is in the middle of implementing. This is the same
/// mitigation `extract_pi_ret` applies on the type side; recorded limit:
/// it covers a stuck head applied at a SUBSTITUTED endpoint, which is
/// every Stage 2/3 shape, and not Stage 5's eta-expanded paths.
def check_path_boundary (checked_body : Term) (parts : PathParts) (scope : Scope)
    (local_types : List Term) (locals : LocalScope) : Result TypeError Term :=
    let at_i0 : Term :=
        normalize_path_boundary (term_subst 0 cub_i0 checked_body) scope local_types locals in
    match unify at_i0 parts.left scope locals {
        err _ => err (TypeError.custom
            "the path body's i0 boundary does not match the type's left endpoint"),
        ok _ =>
            let at_i1 : Term :=
                normalize_path_boundary (term_subst 0 cub_i1 checked_body) scope local_types locals in
            match unify at_i1 parts.right scope locals {
                err _ => err (TypeError.custom
                    "the path body's i1 boundary does not match the type's right endpoint"),
                ok _ => ok at_i0,
            },
    }

/// Normalize a path body's boundary for comparison: weak-head reduce,
/// then rewrite a stuck path application at an endpoint into the
/// endpoint value the path's own type carries, recursing into the
/// arguments of a stuck spine so a boundary like `f (p i0)` (`ap`'s)
/// compares as `f a`, and into constructor arguments so
/// `mk (p i0) (p i0)` (`path_pair`'s) compares as `mk a a`.
///
/// The recursion is bounded by the term itself, not by reduction: every
/// recursive call is on a strict subterm, and `whnf` carries the fuel.
#[partial]
def normalize_path_boundary (t : Term) (scope : Scope) (local_types : List Term)
    (locals : LocalScope) : Term :=
    let t_whnf : Term := whnf scope locals t in
    match term_peel t_whnf {
        Term.app f d =>
            match rewrite_stuck_path_app f d scope local_types locals {
                Option.some boundary => boundary,
                Option.none =>
                    Term.app (normalize_path_boundary f scope local_types locals)
                        (normalize_path_boundary d scope local_types locals),
            },
        Term.con c =>
            match c {
                { name := name, typ_name := typ_name, num_args := num_args, args := cargs } =>
                    let norm_args : List (Option Term) :=
                        normalize_con_args cargs scope local_types locals in
                    let rebuilt : Con :=
                        { name := name, typ_name := typ_name, num_args := num_args, args := norm_args } in
                    Term.con rebuilt,
            },
        _ => t_whnf,
    }

#[partial]
def normalize_con_args (args : List (Option Term)) (scope : Scope) (local_types : List Term)
    (locals : LocalScope) : List (Option Term) :=
    match args {
        List.empty => List.empty,
        List.cons hd rest =>
            match hd {
                Option.some a =>
                    List.cons (Option.some (normalize_path_boundary a scope local_types locals))
                        (normalize_con_args rest scope local_types locals),
                Option.none =>
                    List.cons Option.none (normalize_con_args rest scope local_types locals),
            },
    }

/// `p d` where `p` is a LOCAL path-typed variable and `d` an endpoint:
/// the endpoint value the path's own type carries (`p : PathP A a b`
/// means `p i0 = a`, `p i1 = b` -- the boundary is part of the type, so
/// the comparison is sound, which is why it is a REWRITE rather than a
/// heuristic unification step). `Option.none` unless BOTH hold. A
/// free/global head is refused: a def reference is a `whnf` job, and
/// `normalize_path_boundary` has already given it that chance to unfold
/// into a reducible body. Only the head is path-typed; an applied path
/// under further arguments (`p x i0` -- `funext`'s boundary) is not
/// rewritten here, which is the recorded reason `funext` waits for
/// lambda-eta in `unify` alongside R2.
def rewrite_stuck_path_app (f : Term) (d : Term) (scope : Scope) (local_types : List Term)
    (locals : LocalScope) : Option Term :=
    match term_peel f {
        Term.var idx _dbg =>
            // `if`, not `match`, on the `I64.beq`: the native bool ops
            // (`op_eq`/`op_lt`/`op_gt`/`op_ne`, `term_is_native_bool_op`)
            // compile to a RAW `icmp` i1, and the match scrutinee path
            // would box it with `monad_get_tag` -- a `match` on the result
            // is a codegen trap the corpus never hits (this was its first
            // site). An `if` condition goes through `ensure_i1_cond`,
            // which expects exactly that raw shape.
            if I64.beq idx sentinel then Option.none
            else
                match nth_type idx local_types {
                    Option.none => Option.none,
                    Option.some f_typ =>
                        // Reduced first: a local's declared type can be a
                        // `Path` SPELLED as the library def, and only
                        // `whnf` turns that into the `Term.cubical`
                        // `path_parts_of` recognizes.
                        match path_parts_of (whnf scope locals f_typ) {
                            Option.none => Option.none,
                            Option.some parts =>
                                match endpoint_of (whnf scope locals d) {
                                    Option.some ep =>
                                        match cubical_prim_eq ep CubicalPrim.i0 {
                                            true => Option.some parts.left,
                                            false => Option.some parts.right,
                                        },
                                    Option.none => Option.none,
                                },
                        },
                },
        _ => Option.none,
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
/// Signature-driven application checking: when a `Term.app` spine's head
/// is a free (global) def reference with a registered signature in
/// `ScopeData.def_sigs`, check the WHOLE spine against that signature in
/// one pass -- each argument against its parameter's real declared type
/// (with the type variables solved so far substituted in), collecting
/// the type-variable solution by structurally matching each parameter
/// type against the argument's actual inferred type (`List V` vs
/// `List I64` solves `V := I64`), and returning the substituted return
/// type.
///
/// This is the self-hosted counterpart of the reference checker's own
/// bidirectional application inference (`core_check.rs`). Without it,
/// `type_check_free_var` returning the real signature alone would only
/// move the problem: the application's result type would keep the
/// signature's type variables FREE (`Option V` with `V` unsolved), and
/// match arms on it would fail with "expected A, found I64" exactly as
/// they did when the signature was `Term.hole`.
///
/// `Option.none` everywhere the preconditions don't hold -- head is not
/// a free var, name doesn't resolve, no registered signature, more
/// arguments than parameters (over-application), or any argument failing
/// to check against its real parameter type -- falling back to
/// `type_check_app`'s previous per-layer behavior unchanged (which
/// checks arguments against `Term.hole`, i.e. accepts them, and resolves
/// struct-literal arguments via the named-call fallback).
///
/// That fallback is a CONTRACT, not an oversight: this path is fail-open
/// BY DESIGN relative to the old behavior. An argument-check failure
/// returning `Option.none` means "this checker can't type this call
/// signature-driven; use the old lenient path" -- NOT "reject the
/// program". The same holds for deliberately NOT unifying each
/// argument's inferred type against its substituted parameter type: a
/// mismatch there would, if it errored, only relocate the leniency (the
/// `err` would bubble to `Option.none` and the old path, which checks
/// against `Term.hole`, would accept the same argument anyway) -- there
/// is no soundness delta available through this path, only a loss of
/// return-type precision. What WAS tightened here (partial-application
/// residual pi chain, local-shadow guard, concrete-type-name solving
/// gate) is the subset that could previously commit a WRONG result
/// rather than merely a lenient one. The hard checking stays with the
/// reference checker (`core_check.rs`) and the Rust host's `check`.
#[partial]
def try_type_check_def_call (app_term : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Option (Result TypeError TypedTerm) :=
    match flatten_call_spine app_term {
        CallSpine.mk head args =>
            // `f #Named.Instance args` -- the hint markers ride the spine's
            // head (lowering puts them in the FIRST argument slot). Peel
            // them before the arity check counts arguments; they are
            // validated right after the callee resolves and re-attached to
            // the rebuilt term at the bottom, so the codegen dict pass
            // still sees the hint.
            match strip_dict_hint_args args {
                Pair.pair dict_hints real_args =>
            match head {
                Term.var idx dbg =>
                    match dbg {
                        DebugName.named id =>
                            if not (I64.beq idx sentinel) then Option.none
                            // A LOCAL of this name shadows any global of
                            // the same name, and a local's own type is
                            // not a registered signature. Without this
                            // guard `scope_resolve_name` correctly returns
                            // the LOCAL's `ScopeDef`, but its `.name` is
                            // the same single-segment `NamePath` the
                            // global is registered under -- so the
                            // `def_sigs` lookup below would hand back the
                            // GLOBAL's signature and check this call's
                            // arguments against the wrong parameter types
                            // (`def danger (pick : String -> I64) ... :=
                            // pick s`, with an unrelated global `pick`).
                            // Today that degrades to `Option.none` rather
                            // than a false error, since `def_call_check_
                            // args` infers each argument intrinsically
                            // first and any failure bails out -- but that
                            // is luck, not design; a shadowed name whose
                            // arguments happened to fit the global's
                            // parameters would silently type against the
                            // wrong signature.
                            else if is_some_local (scope_find_local id locals) then Option.none
                            else
                                match scope_resolve_name (NameRef.nid id) scope locals {
                                    err _ => Option.none,
                                    ok sd =>
                                        match sd {
                                            mk resolved_name _ _ _ _ =>
                                                match validate_dict_hints id (Option.some resolved_name) dict_hints scope {
                                                    Option.some e => Option.some (err e),
                                                    Option.none =>
                                                match scope_find_def_sig resolved_name scope {
                                                    Option.none => Option.none,
                                                    Option.some sig =>
                                                        // Phase 3's leading dict Pis are not
                                                        // arguments of the call being solved;
                                                        // keeping them here shifted every
                                                        // parameter left by one.
                                                        let k : I64 := count_dict_pis sig in
                                                        match sig_tvars_params_ret (strip_dict_pis sig k) {
                                                            SigInfo.mk params ret =>
                                                                if I64.gt (List.length real_args) (List.length params)
                                                                then Option.none
                                                                else
                                                                    // Seed the substitution from the arguments whose
                                                                    // own type is recoverable INTRINSICALLY before any
                                                                    // argument is paired -- see `presolve_def_args`.
                                                                    let pre : List (Pair Identifier Term) :=
                                                                        presolve_def_args real_args params scope local_types locals List.empty in
                                                                    // ...and again from the RETURN direction BEFORE
                                                                    // the arguments are checked. A parameter type
                                                                    // that mentions a class variable (`HtmlT M I J A`
                                                                    // in `HtmlT.map f ma`) otherwise hands an
                                                                    // abstract carrier to every nested constrained
                                                                    // call in its argument (`HtmlT.body_node ...`
                                                                    // gets `HtmlT M I J A`, cannot resolve
                                                                    // `[Monad M]`, and codegen later turns it into a
                                                                    // partial application waiting for a dictionary).
                                                                    // The expectation is the same evidence the return
                                                                    // direction already uses below, one step earlier;
                                                                    // the intrinsic-argument presolve keeps precedence
                                                                    // because `solve_typevars` never overwrites.
                                                                    let ret_seed : List (Pair Identifier Term) :=
                                                                        drop_no_progress_bindings
                                                                            (solve_typevars scope (rebuild_pi_chain (drop_params (List.length real_args) params) ret) expected_type List.empty) in
                                                                    match def_call_check_args real_args params (List.append pre ret_seed) List.empty scope local_types locals {
                                                                        // A decline means "type this call another
                                                                        // way", the pre-existing contract. A solved
                                                                        // mismatch is not that: the ordinary path
                                                                        // would check the same argument against
                                                                        // `Term.hole` and accept it, so the error
                                                                        // escapes the probe the way
                                                                        // `validate_dict_hints`' own hard error
                                                                        // does (`Option.some (err e)` above).
                                                                        CallArgOutcome.call_args_decline => Option.none,
                                                                        CallArgOutcome.call_args_type_error e => Option.some (err e),
                                                                        CallArgOutcome.call_args_ok pair =>
                                                                            match pair {
                                                                                DccPair.mk elab_args subst levels =>
                                                                                    // A PARTIAL application's type is the
                                                                                    // remaining pi chain, not the final
                                                                                    // return type: `add2 1` (of `def add2
                                                                                    // (a : I64) (b : I64) : I64`) is
                                                                                    // `I64 -> I64`, not `I64`. Returning
                                                                                    // `ret` unconditionally accepted
                                                                                    // `def wrong : I64 := add2 1`, which
                                                                                    // the reference checker rejects.
                                                                                    let full_ret : Term :=
                                                                                        rebuild_pi_chain (drop_params (List.length real_args) params) ret in
                                                                                    // W1.4: the LEVEL instantiation runs
                                                                                    // beside the type-variable one. A
                                                                                    // declared `: Sort u` return type
                                                                                    // (`def lift (A : Sort u) : Sort u`)
                                                                                    // otherwise came back still naming
                                                                                    // `u`, and `unify_sort`
                                                                                    // (`lang/typecheck/unify.mo`) answers
                                                                                    // `false` for an unresolved level, so
                                                                                    // the call's own type could never
                                                                                    // match a concrete expectation.
                                                                                    let subst_ret : Term :=
                                                                                        subst_levels_term (subst_typevars_term full_ret subst) levels in
                                                                                    // SOLVE THE RETURN DIRECTION.
                                                                                    // The argument direction above can
                                                                                    // only solve a type variable the
                                                                                    // arguments themselves mention, and
                                                                                    // the arguments this infer-only
                                                                                    // checker types as a hole are
                                                                                    // exactly the common ones -- a
                                                                                    // PARAMETERIZED inductive's
                                                                                    // constructor application
                                                                                    // (`List.cons h t`, `Option.some x`)
                                                                                    // has no recoverable type at all
                                                                                    // (`con_ref_result_type` declines
                                                                                    // it by design). The call then came
                                                                                    // back with its signature's raw `IO
                                                                                    // A` still free, and reported it as
                                                                                    // a mismatch the moment a match arm
                                                                                    // unified it against the def's own
                                                                                    // declared `IO (List I64)`
                                                                                    // (`std/src/concurrent/combine_test.
                                                                                    // mo`'s `all_i64`, `a`'s arms). The
                                                                                    // ambient expected type is the same
                                                                                    // kind of already-elaborated
                                                                                    // information the argument direction
                                                                                    // solves from, one position over, so
                                                                                    // solve it the same way and apply it
                                                                                    // through the same substitution.
                                                                                    // Purely additive: with nothing left
                                                                                    // to solve the substitution comes
                                                                                    // back empty and every term below is
                                                                                    // unchanged.
                                                                                    let ret_subst : List (Pair Identifier Term) :=
                                                                                        solve_typevars scope subst_ret expected_type List.empty in
                                                                                    let refined_ret : Term := subst_typevars_term subst_ret ret_subst in
                                                                                    // `refined_ret`, NOT the unification's answer.
                                                                                    // It used to be
                                                                                    // `match unify_structural refined_ret
                                                                                    // expected_type { ok u => u, err _ =>
                                                                                    // refined_ret }`, and `unify_go`'s Pi arm
                                                                                    // answers the unified CODOMAIN -- so a
                                                                                    // PARTIAL application under a Pi expectation
                                                                                    // came back one arrow short. `def p : I64 ->
                                                                                    // I64 := q 1` (two-parameter `q`) typed its
                                                                                    // body `I64`, which the def boundary then
                                                                                    // rejected; and every partially applied def
                                                                                    // passed as an argument
                                                                                    // (`List.map (prefixed "a_") xs`) typed as
                                                                                    // its full result, which the call-argument
                                                                                    // check reported on 60+ corpus sites. A hole
                                                                                    // return type is the one case the expectation
                                                                                    // still improves on (`unify hole e` answers
                                                                                    // `e`), so that keeps the unification.
                                                                                    let result_typ : Term :=
                                                                                        call_result_typ refined_ret expected_type scope locals in
                                                                                    // Re-attach the peeled `#` markers ahead of
                                                                                    // the elaborated arguments (the dict pass reads
                                                                                    // the hint off them) and insert the callee's
                                                                                    // dict argument(s) behind them.
                                                                                    let rebuilt : Term :=
                                                                                        reify_ordinary_dict_args resolved_name k dict_hints (dict_hint_marker_terms dict_hints) subst ret_subst expected_type scope locals head elab_args in
                                                                                    Option.some (ok (mk_typed rebuilt result_typ)),
                                                                            },
                                                                    },
                                                        },
                                                },
                                        },
                                        },
                                },
                        DebugName.unnamed => Option.none,
                    },
                _ => Option.none,
            },
            },
    }

/// `App`-spine probe for a CONSTRUCTOR reference callee (`ResultT.mk arg`,
/// `List.cons h t`, ...) -- the ordinary prefix-call spelling every
/// constructor application outside struct-literal/named-call syntax uses
/// (`type_check_con`'s own doc comment: "the parser never builds
/// `Term.con`"). `try_type_check_def_call` already declines these
/// outright (a constructor has no `def_sigs` entry), so without this
/// probe a constructor's arguments are checked bottom-up, intrinsic-first
/// (`type_check_app_ordinary`'s own order, via `con_ref_result_type`
/// trusting whatever Pi `type_check_app`'s recursion already built from
/// the ARGUMENT's own inferred type) -- fine when an argument reveals the
/// constructor's own type params on its own, but a parameter typed in
/// terms of the OWNING type's params (`ResultT.mk`'s `run : M (Result E
/// A)`) can have an argument that carries NO information of its own about
/// `M` (a `do`-block ending in a bare `Monad.pure` call: `pure`'s only
/// argument never mentions the monad it targets). Only the OUTER
/// `expected_type`, via this constructor's own RETURN type (always
/// exactly its owning type applied to its own params), can recover it --
/// and unlike an ordinary def, a constructor's return type ALWAYS names
/// every one of its own params, so solving from `expected_type` FIRST
/// (before looking at any argument) strictly dominates the argument-
/// direction solving `def_call_check_args` uses for ordinary defs.
/// Reuses `con_own_param_bindings`, the same carrier recovery
/// `check_con_args_against_params` already uses for struct-literal/
/// named-call syntax.
///
/// `Option.none` (defer to the existing bottom-up path, unchanged)
/// whenever the spine's head isn't a bare, unshadowed constructor
/// reference, its arity doesn't match, OR `con_own_param_bindings` comes
/// back empty -- an uninformative `expected_type` means this probe would
/// check each argument against the constructor's own ABSTRACT param
/// types (bare, unbound type variables), which is not equivalent to the
/// existing path's `Term.hole` (no expectation at all) and could reject
/// an argument the old path accepted. Taking over only when a real
/// substitution exists keeps this purely additive, matching
/// `con_result_type`'s own "only ever ADD precision, never override"
/// discipline.
/// Resolve a (possibly-qualified) constructor reference to its OWNING
/// inductive. Prefers the QUALIFIED lookup (`scope_find_inductive` on the
/// text before the last dot, e.g. `ResultT` in `ResultT.mk`) when `id`
/// actually carries one -- `scope_find_inductive_by_constructor con_mp`
/// (the fallback, and `type_check_free_var_con`'s own ONLY lookup) scans
/// EVERY registered inductive for ONE owning a constructor named like
/// `con_mp` and returns the FIRST match (`find_inductive_by_constructor_
/// in_pairs`, `lang/scope.mo`) -- sound enough for `type_check_free_var_
/// con`'s own purpose (confirming SOME inductive owns this ctor name,
/// then trusting `expected_type` verbatim regardless of which), but
/// `con_own_param_bindings` below needs the ACTUAL owning type, and `mk`
/// is this corpus's single most common constructor name (every struct's
/// own synthetic constructor) -- an unqualified scan would, in practice,
/// resolve `ResultT.mk` to some unrelated FIRST-in-hashmap-order struct
/// instead, computing bindings for the wrong type entirely (silently:
/// `bind_term_vars` just fails to match and returns no bindings, so this
/// probe harmlessly declines rather than miscompiling -- confirmed via a
/// forced diagnostic, not assumed). Falls back to the ambiguous scan only
/// when `id` has no qualifier, or the qualifier doesn't name a real
/// inductive (a local alias, a module path segment, ...).
#[partial]
def con_call_resolve_inductive (id : Identifier) (con_mp : NamePath) (scope : Scope) : Option Inductive :=
    match id {
        Identifier.id s =>
            match dotted_qualifier s {
                Option.some q =>
                    match scope_find_inductive (NamePath.mk (List.cons (Identifier.id q) List.empty)) scope {
                        ok ind => Option.some ind,
                        err _ => scope_find_inductive_by_constructor con_mp scope,
                    },
                Option.none => scope_find_inductive_by_constructor con_mp scope,
            },
    }

#[terminating]
def try_type_check_con_call (app_term : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Option (Result TypeError TypedTerm) :=
    match flatten_call_spine app_term {
        CallSpine.mk head args =>
            match head {
                Term.var idx dbg =>
                    match dbg {
                        // An unnamed variable carries no name to resolve a
                        // constructor by -- the same "insufficient evidence,
                        // decline" answer this function already gives for
                        // every other non-matching head shape.
                        DebugName.unnamed => Option.none,
                        DebugName.named id =>
                            if not (I64.beq idx sentinel) then Option.none
                            else if is_some_local (scope_find_local id locals) then Option.none
                            // A reference `SomeClass.method` is never a constructor
                            // application, even when a constructor of the same bare
                            // name exists: `con_call_resolve_inductive` falls back to
                            // the bare-constructor scan when the qualifier is not an
                            // inductive, and `Sub.sub` (the `(-)` infix) then resolves
                            // to `LLVMValue`'s own `sub` constructor, whose fields are
                            // `LLVMValue`. Declining here leaves it to the class-method
                            // path, which is what it is.
                            else if qualified_by_class id scope then Option.none
                            else
                                let bare_name : Identifier := match id { Identifier.id s => Identifier.id (last_dotted_segment s) } in
                                let con_mp : NamePath := NamePath.mk (List.cons bare_name List.empty) in
                                match con_call_resolve_inductive id con_mp scope {
                                    Option.none => Option.none,
                                    Option.some ind =>
                                        match find_constructor_in_inductive ind con_mp {
                                            Option.none => Option.none,
                                            Option.some ctor =>
                                                match ctor {
                                                    InductConstructor.mk con_name params _ =>
                                                        if not (I64.beq (List.length args) (List.length params)) then Option.none
                                                        else
                                                            let bindings : List (Pair Identifier Term) := con_own_param_bindings ind expected_type in
                                                            match con_call_check_args_solving ind args params bindings scope local_types locals {
                                                                // Empty `bindings` is the pre-port DECLINE case
                                                                // (`con_own_param_bindings` found nothing in the
                                                                // expectation): the old probe returned `Option.none`
                                                                // before checking any argument, so an argument that
                                                                // does not fit the constructor's ABSTRACT parameters
                                                                // fell through to the bottom-up path instead of
                                                                // failing here. Keep that: only a probe that already
                                                                // knew the constructor's params may report an error.
                                                                err e => if List.is_empty bindings then Option.none else Option.some (err e),
                                                                ok pair =>
                                                                    match pair {
                                                                        Pair.pair elab_args final_bindings =>
                                                                            // The applied result is only a real answer when the
                                                                            // constructor name is unambiguous, or the source
                                                                            // qualified it: `cons` belongs to both `List` and
                                                                            // `Vec`, and the bare scan can pick either
                                                                            // (`con_call_resolve_inductive`'s own ambiguity) --
                                                                            // handing the call a wrong concrete type instead of
                                                                            // the old hole, which measurably mis-typed
                                                                            // `cli/src/main.mo`'s list code.
                                                                            let usable : Bool :=
                                                                                match id {
                                                                                    Identifier.id s =>
                                                                                        match dotted_qualifier s {
                                                                                            Option.some _ => true,
                                                                                            Option.none => I64.beq (List.length (scope_find_all_inductives_by_constructor con_mp scope)) 1,
                                                                                        },
                                                                                } in
                                                                            // Keep the EXPECTED type whenever it already names this
                                                                            // inductive: its spelling is the one the rest of the term
                                                                            // uses (`Toml.Line`, a dotted declaration name), and the
                                                                            // bare name `inductive_bare_name` yields would mismatch it
                                                                            // literally (`expected Toml.Line, found Line`). The applied
                                                                            // result exists for the case the expectation does NOT name it
                                                                            // (`some 42` against `F A`).
                                                                            let expected_names : Bool :=
                                                                                match type_head_name (term_peel expected_type) {
                                                                                    Option.some h => String.beq (identifier_tail h) (identifier_tail (inductive_bare_name ind)),
                                                                                    Option.none => false,
                                                                                } in
                                                                            match (if usable && Bool.not expected_names then con_applied_result_type ind final_bindings else Option.none) {
                                                                                Option.some result_typ =>
                                                                                    let c : Con := Con.mk (struct_lit_con_name con_name) (inductive_type_path ind) (List.length params) (wrap_all_some elab_args) in
                                                                                    Option.some (ok (mk_typed (Term.con c) result_typ)),
                                                                                // Nothing solved: the old answers still apply.
                                                                                Option.none =>
                                                                                    if List.is_empty bindings
                                                                                    then Option.none
                                                                                    else
                                                                                        let c : Con := Con.mk (struct_lit_con_name con_name) (inductive_type_path ind) (List.length params) (wrap_all_some elab_args) in
                                                                                        Option.some (ok (mk_typed (Term.con c) (con_result_type ind expected_type))),
                                                                            },
                                                                    },
                                                            },
                                                }
                                        },
                                },
                    },
                _ => Option.none,
            },
    }

/// `try_type_check_con_call`'s argument loop: every argument checked
/// TOP-DOWN against its own (bindings-substituted) declared param type,
/// with the constructor's OWN type params bound as each argument's
/// inferred type comes back -- `some 42` therefore yields `Option I64`
/// even when nothing in the expected type says so.
///
/// That argument-side source is what the checker lacked: the retired
/// syntactic pass inferred it (`infer_carrier_type`), and without it a
/// bare constructor application stayed a HOLE by design
/// (`con_ref_result_type` declines applied forms), which starved every
/// consumer downstream -- `def_call_check_args` could not bind
/// `F A := Option I64`, so `class_method_next_param` handed a lambda
/// argument the class's still-abstract `A -> B -> B`, and
/// `Foldable.foldl (fn acc x => acc + x) 0 (some 42)` left `acc + x`
/// unresolved.
#[partial]
def con_call_check_args_solving (ind : Inductive) (args : List Term) (params : List Param) (bindings : List (Pair Identifier Term)) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError (Pair (List Term) (List (Pair Identifier Term))) :=
    match args {
        List.empty => ok (Pair.pair List.empty bindings),
        List.cons a rest =>
            match params {
                List.empty => err (TypeError.custom "constructor arity mismatch"),
                List.cons p prest =>
                    match p {
                        Param.mk _ ptyp _ _ _ =>
                            let field_typ : Term := apply_con_param_bindings bindings ptyp in
                            match type_check a field_typ scope local_types locals {
                                err e => err e,
                                ok a_tt =>
                                    let more : List (Pair Identifier Term) :=
                                        bind_term_vars (inductive_param_names ind) field_typ a_tt.typ bindings in
                                    match con_call_check_args_solving ind rest prest more scope local_types locals {
                                        err e => err e,
                                        ok tail =>
                                            match tail {
                                                Pair.pair rest_elab rest_bindings =>
                                                    ok (Pair.pair (List.cons a_tt.term rest_elab) rest_bindings),
                                            },
                                    },
                            },
                    },
            },
    }

/// `ind`'s own declared type-parameter names -- the wildcard set
/// `bind_term_vars` matches a constructor's field type against an
/// argument's inferred type with.
#[partial]
def inductive_param_names (ind : Inductive) : List Identifier :=
    match ind { Inductive.mk _ params _ _ _ _ => param_names params }

/// `ind`'s head applied to every one of its own params, substituted with
/// the bindings the call site solved (`Option I64` for `some 42`).
/// `Option.none` while any param is unbound -- the call site then knows
/// no more than it did, and the other result-type paths answer.
#[partial]
def con_applied_result_type (ind : Inductive) (bindings : List (Pair Identifier Term)) : Option Term :=
    con_applied_result_go (Term.var sentinel (DebugName.named (inductive_bare_name ind))) (inductive_param_names ind) bindings

#[partial]
def con_applied_result_go (head : Term) (names : List Identifier) (bindings : List (Pair Identifier Term)) : Option Term :=
    match names {
        List.empty => Option.some head,
        List.cons n rest =>
            match binding_of bindings n {
                Option.some t => match con_applied_result_go (Term.app head t) rest bindings {
                    Option.some r => Option.some r,
                    Option.none => Option.none,
                },
                Option.none => Option.none,
            },
    }

#[partial]
def wrap_all_some (xs : List Term) : List (Option Term) :=
    match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons (Option.some x) (wrap_all_some rest),
    }

/// `Option.some`-ness test for a `LocalVar` lookup -- `try_type_check_
/// def_call`'s shadow guard only needs to know WHETHER a local of that
/// name exists, not what it is.
#[partial]
def is_some_local (lv : Option LocalVar) : Bool :=
    match lv {
        Option.some _ => true,
        Option.none => false,
    }

/// Drop the first `n` entries of a parameter-type list -- the ones a
/// call actually supplied arguments for. What remains is the callee's
/// still-unapplied parameters (empty for a saturated call).
#[partial]
def drop_params (n : I64) (params : List Term) : List Term :=
    if I64.lt n 1 then params
    else
        match params {
            List.empty => List.empty,
            List.cons _ rest => drop_params (n - 1) rest,
        }

/// The type a signature-driven call reports: the residual Pi chain, NOT
/// what `unify_structural` answers.
///
/// `unify_go`'s Pi arm returns the unified CODOMAIN (its own doc: "Pi
/// matches Pi structurally"), so using its answer as the call's type made
/// every PARTIAL application under a Pi expectation come back one arrow
/// short: `def p : I64 -> I64 := q 1` (two-parameter `q`) typed its body
/// `I64`, and `List.map (prefixed "a_") xs` typed the argument `String`
/// instead of `String -> String`. A HOLE return type is the one case the
/// expectation genuinely improves on (`unify hole e` answers `e`), so the
/// unification is kept there and only there.
def call_result_typ (refined_ret : Term) (expected_type : Term)
    (scope : Scope) (locals : LocalScope) : Term :=
    if is_hole (term_peel refined_ret) then
        match unify_structural refined_ret expected_type scope locals {
            ok u => u,
            err _ => refined_ret,
        }
    else refined_ret

/// Rebuild a `Term.pi` chain over `ret` from the still-unapplied
/// parameter types, right-associated: `[A, B]` over `R` gives
/// `Pi A (Pi B R)`. Empty list (a saturated call) gives `ret` itself,
/// so the common case is unchanged.
#[partial]
def rebuild_pi_chain (params : List Term) (ret : Term) : Term :=
    match params {
        List.empty => ret,
        List.cons p rest => Term.pi binder_anon p (rebuild_pi_chain rest ret),
    }

pub struct DccPair {
    elab_args : List Term,
    subst : List (Pair Identifier Term),
    /// Level variables solved from the arguments so far (W1.4), keyed by
    /// name exactly like `subst` is keyed by type variable. Threaded
    /// beside `subst` rather than inside it because a `SortLevel` is not a
    /// `Term`; `try_type_check_def_call` applies it to the return type
    /// with `subst_levels_term`.
    levels : List (Pair Identifier SortLevel),
}

/// What the signature-driven argument loop concluded, in three cases
/// rather than two.
///
/// The probe is fail-open by design (`try_type_check_def_call`'s own doc
/// comment): "this checker could not type this call this way" must fall
/// back to the ordinary path, so most failures are a DECLINE --
/// `call_args_decline`, which every pre-existing `err` maps to.
///
/// `call_args_type_error` is a real mismatch: the argument's type was
/// inferred, the parameter's type was fully solved, and the two do not
/// match. Falling back cannot rescue that -- the ordinary path checks
/// the argument against `Term.hole`, i.e. accepts anything -- so the
/// error has to escape. `try_type_check_def_call` returns it the way it
/// already returns `validate_dict_hints`' own hard error.
///
/// `call_args_ok` carries the loop's result unchanged.
pub type CallArgOutcome {
    call_args_ok (pair : DccPair),
    call_args_decline,
    call_args_type_error (err : TypeError),
}

/// `try_type_check_def_call`'s argument loop: infer each argument's own
/// type, solve this parameter's remaining type variables against it,
/// and recurse (with the solutions so far substituted into the later
/// parameter types). Any argument check failure is an `err` (the caller
/// falls back to `type_check_app`'s previous behavior, preserving its
/// leniency).
///
/// The argument is inferred INTRINSICALLY first (checked against
/// `Term.hole`): checking it against the parameter type directly would
/// fail whenever that parameter still mentions an UNSOLVED type
/// variable (`List V` vs the concrete `List I64` -- this checker's
/// `unify` does no typevar solving), and an argument checked against
/// the typevar-carrying param type can come back POLLUTED with the
/// unsolved var itself, leaving nothing to solve from. Only arguments
/// that cannot be inferred in isolation -- a struct literal, which
/// needs its expected type to know which struct it is -- fall back to
/// checking against the parameter type itself.
/// Solve a def call's type variables from the arguments whose own type is
/// recoverable INTRINSICALLY, before any argument is paired with its
/// parameter. Arguments are otherwise paired strictly left-to-right, so a
/// higher-order FIRST argument (`Array.foldl (fn acc x => acc + x) 0 a`) is
/// checked against the still-abstract `B -> A -> B`, and the class calls
/// inside the lambda (`acc + x`) have no carrier -- even though the LATER
/// arguments pin both variables. The retired syntactic pass pre-solved the
/// same way per call site (`call_arg_hints`).
#[partial]
def presolve_def_args (args : List Term) (params : List Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) (acc : List (Pair Identifier Term)) : List (Pair Identifier Term) :=
    match args {
        List.empty => acc,
        List.cons arg rest =>
            match params {
                List.empty => acc,
                List.cons param_ty rest_params =>
                    match type_check arg Term.hole scope local_types locals {
                        err _ => presolve_def_args rest rest_params scope local_types locals acc,
                        // An argument that still carries a class-method call was
                        // only PARTLY resolved (a list literal's
                        // `FromListLiteral.empty` with nothing yet to read its
                        // carrier from). Binding its type into the call's
                        // substitution poisons the parameters every later
                        // argument -- and the enclosing expectation -- are
                        // checked against, MEASURED as a self-compile failure
                        // (`lang.module::coverage_warning_of_match`'s `[]`).
                        ok a_tt =>
                            if mentions_class_method_ref a_tt.term scope locals
                            then presolve_def_args rest rest_params scope local_types locals acc
                            else presolve_def_args rest rest_params scope local_types locals
                                (drop_no_progress_bindings (solve_typevars scope param_ty a_tt.typ acc)),
                    },
            },
    }

/// A binding `X := X` (or `X := hole`) is no information, and worse than
/// none: `lookup_binding` returns the FIRST entry for a name and
/// `solve_typevars` never overwrites, so leaving one in the accumulator
/// hides every later, real binding. MEASURED: `outer id (inner 41)` where
/// `outer [Monad M] (f : A -> B) (m : M A)` -- the second argument's own
/// still-abstract type is `M A`, so presolve recorded `M := M`, the return
/// direction's `M := IO` was then ignored, `[Monad M]` had no informative
/// carrier, and BOTH calls compiled as partial applications waiting for a
/// dictionary (codegen's arity saw an argument missing) -- the oak
/// `HtmlT.map` / `html_t_tests` SIGSEGV. The same self-binding arises for
/// a list literal's nested `FromListLiteral.cons` (`L A` against `L A`).
#[partial]
def binding_no_progress (k : Identifier) (t : Term) : Bool :=
    match term_peel t {
        Term.hole => true,
        Term.var _ dbg => match dbg {
            DebugName.named id => id_eq id k,
            DebugName.unnamed => true,
        },
        _ => false,
    }

#[partial]
def drop_no_progress_bindings (bs : List (Pair Identifier Term)) : List (Pair Identifier Term) :=
    match bs {
        List.empty => List.empty,
        List.cons b rest => match b {
            Pair.pair k t =>
                if binding_no_progress k t
                then drop_no_progress_bindings rest
                else List.cons b (drop_no_progress_bindings rest),
        },
    }

#[partial]
def def_call_check_args (args : List Term) (params : List Term) (subst : List (Pair Identifier Term)) (levels : List (Pair Identifier SortLevel)) (scope : Scope) (local_types : List Term) (locals : LocalScope) : CallArgOutcome :=
    match args {
        List.empty => CallArgOutcome.call_args_ok (DccPair.mk List.empty subst levels),
        List.cons arg rest =>
            match params {
                List.empty => CallArgOutcome.call_args_decline,
                List.cons param_ty rest_params =>
                    // Levels solved by the arguments BEFORE this one
                    // (W1.4) reach this parameter's type, so a later
                    // `(B : Sort u)` is checked at the instantiated `u`.
                    let a_expected : Term := subst_levels_term (subst_typevars_term param_ty subst) levels in
                    // A CALL argument gets the parameter type as its
                    // expectation when that type is fully solved: a nested
                    // constrained call (`outer id (inner 41)`,
                    // `HtmlT.map f (HtmlT.body_node n)`) can only resolve
                    // its own dictionary from it. This REPLACES the
                    // intrinsic pass rather than adding one -- re-checking
                    // after the fact re-elaborated the whole subtree at
                    // every nesting level and was a measured ~100x
                    // slowdown on `monad check examples`. Every other
                    // argument, and any parameter still carrying an
                    // unsolved variable (opened to holes by
                    // `open_free_type_vars`), keeps the pre-existing
                    // intrinsic behavior.
                    let want : Term := open_free_type_vars a_expected scope in
                    let prefer : Bool :=
                        match term_peel arg {
                            Term.app _ _ => Bool.not (mentions_hole want),
                            _ => false,
                        } in
                    match check_arg_for_call prefer arg want scope local_types locals {
                        ok a_tt0 =>
                            let a_tt : TypedTerm := recheck_unresolved_class_calls arg a_tt0 a_expected scope local_types locals in
                            def_call_continue arg a_tt param_ty rest rest_params subst levels scope local_types locals,
                        err _ =>
                            // Same vacuous-success trap `type_check_app`
                            // guards against (see `struct_literal_arg_
                            // matches_expected`): an unannotated struct
                            // literal "checks" against ANY registered
                            // inductive's first constructor, fields
                            // unexamined. This fast path has no named-call
                            // spread of its own to fall back to, so it must
                            // DECLINE outright -- `try_type_check_def_call`
                            // turns this `err` into `Option.none` and
                            // `type_check_app`'s own guarded path (which
                            // does have the spread) handles the call
                            // correctly. Without this, a bare literal
                            // argument to a def whose matching param is a
                            // registered inductive (`file_path : String`)
                            // committed here as an empty constructor.
                            // Every failure on this path stays a DECLINE
                            // (`call_args_decline`), exactly as the `err`
                            // it replaces did.
                            if not (struct_literal_arg_matches_expected arg a_expected scope)
                            then CallArgOutcome.call_args_decline
                            else
                            match type_check arg a_expected scope local_types locals {
                                err _ => CallArgOutcome.call_args_decline,
                                ok a_tt =>
                                    def_call_continue arg a_tt param_ty rest rest_params subst levels scope local_types locals,
                            },
                    },
            },
    }

/// The argument check `def_call_check_args` runs: the expectation when the
/// argument is a CALL and `prefer`, else intrinsic inference. A failed
/// expectation check falls back to the intrinsic one, preserving the old
/// leniency for an argument that cannot be checked that way.
///
/// A result that STILL mentions a class-method ref falls back as well.
/// The expectation turns the nested call onto `try_type_check_def_call`'s
/// infer-only path, which commits an elaboration the intrinsic pass would
/// otherwise have declined -- and this function cannot tell "solved it
/// with the expectation" from "accepted it without solving". The test is
/// `recheck_unresolved_class_calls`'s own: a term still naming
/// `HAdd.add` has no carrier, since every resolved one is rewritten to a
/// dictionary projection. MEASURED: `Comonad.extend (fn a => Id.run a +
/// 1) (Id.id 41)` inside `Id.run (...)` -- the outer call expected `Id
/// A`, the inner `extend` was checked against it, and codegen died with
/// `no instance found for prelude::HAdd.add` (`init/src/tests.mo`'s
/// comonad-id extend test), while the intrinsic pass leaves the call for
/// `type_check_app` to resolve against the callee's own domain.
#[partial]
def check_arg_for_call (prefer : Bool) (arg : Term) (want : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    if prefer
    then
        match type_check arg want scope local_types locals {
            ok tt =>
                if mentions_class_method_ref tt.term scope locals
                then type_check arg Term.hole scope local_types locals
                else ok tt,
            err _ => type_check arg Term.hole scope local_types locals,
        }
    else type_check arg Term.hole scope local_types locals

/// An argument inferred in isolation leaves a class-method call whose carrier
/// only the PARAMETER type can supply (`len [1, 2]`: the literal's
/// `FromListLiteral.cons` has nothing else to read `List` from). Re-check it
/// against that parameter type with its still-unsolved variables opened to holes,
/// and keep the result only if it resolved what the isolated check did not.
#[partial]
def recheck_unresolved_class_calls (arg : Term) (a_tt : TypedTerm) (a_expected : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : TypedTerm :=
    if not (mentions_class_method_ref a_tt.term scope locals) then a_tt
    else
        let want : Term := open_free_type_vars a_expected scope in
        if not (has_informative_head want) then a_tt
        else
            match type_check arg want scope local_types locals {
                err _ => a_tt,
                ok b_tt => if mentions_class_method_ref b_tt.term scope locals then a_tt else b_tt,
            }

/// An argument checked with no expectation (`J.arr [a, b]`: a constructor is no
/// def call) can leave a class-method call whose carrier only the callee's
/// parameter type supplies. Re-check it against that domain, with the callee's
/// own type variables solved from the call's expected result where it names them.
#[partial]
def recheck_against_callee_domain (f : Term) (arg : Term) (a_tt : TypedTerm) (a_expected : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : TypedTerm :=
    if not (is_hole a_expected) then a_tt
    else if not (mentions_class_method_ref a_tt.term scope locals) then a_tt
    else
        match ctor_field_domain f expected_type scope {
            Option.some dom => recheck_unresolved_class_calls arg a_tt dom scope local_types locals,
            Option.none =>
                match type_check f Term.hole scope local_types locals {
                    err _ => a_tt,
                    ok f_tt =>
                        match pi_domain_of f_tt.typ {
                            Option.none => a_tt,
                            Option.some dom =>
                                let solved : List (Pair Identifier Term) :=
                                    solve_typevars scope (final_result_type f_tt.typ) (final_result_type expected_type) List.empty in
                                recheck_unresolved_class_calls arg a_tt (subst_typevars_term dom solved) scope local_types locals
                        },
                },
        }

/// The declared type of the field a constructor application's next argument
/// fills (`J.arr` in `J.arr xs`: `List J`), with the inductive's own parameters
/// solved from the call's expected result. A constructor has no stored
/// signature, so `type_check` of its name says nothing about its fields.
#[partial]
def ctor_field_domain (f : Term) (expected_type : Term) (scope : Scope) : Option Term :=
    match flatten_call_spine f {
        CallSpine.mk head args =>
            match term_peel head {
                Term.var idx dbg =>
                    match dbg {
                        DebugName.unnamed => Option.none,
                        DebugName.named id =>
                            if not (I64.beq idx sentinel) then Option.none
                            else
                                let bare_name : Identifier := match id { Identifier.id s => Identifier.id (last_dotted_segment s) } in
                                let con_mp : NamePath := NamePath.mk (List.cons bare_name List.empty) in
                                let owner : Option Inductive :=
                                    match id {
                                        Identifier.id s =>
                                            match dotted_qualifier s {
                                                Option.some qual =>
                                                    match scope_find_inductive (NamePath.mk (List.cons (Identifier.id qual) List.empty)) scope {
                                                        ok ind => Option.some ind,
                                                        err _ => scope_find_inductive_by_constructor con_mp scope,
                                                    },
                                                Option.none => scope_find_inductive_by_constructor con_mp scope,
                                            },
                                    } in
                                match owner {
                                    Option.none => Option.none,
                                    Option.some ind =>
                                        match find_constructor_in_inductive ind con_mp {
                                            Option.none => Option.none,
                                            Option.some ctor =>
                                                match ctor {
                                                    InductConstructor.mk _ fields _ =>
                                                        match nth_type (List.length args) (List.map param_type fields) {
                                                            Option.none => Option.none,
                                                            Option.some field_ty =>
                                                                Option.some (subst_typevars_term field_ty (ctor_param_solution ind scope expected_type)),
                                                        },
                                                },
                                        },
                                },
                    },
                _ => Option.none,
            },
    }

def param_type (p : Param) : Term :=
    match p {
        Param.mk _ t _ _ _ => t,
    }

#[partial]
def apply_param_vars (head : Term) (params : List Param) : Term :=
    match params {
        List.empty => head,
        List.cons p rest =>
            match p {
                Param.mk n _ _ _ _ => apply_param_vars (Term.app head (Term.var sentinel (DebugName.named n))) rest,
            },
    }

/// The inductive's own parameters (`K`, `V` of `BT K V`) read off the call's
/// expected result type.
def ctor_param_solution (ind : Inductive) (scope : Scope) (expected_type : Term) : List (Pair Identifier Term) :=
    match ind {
        Inductive.mk _ params _ _ _ _ =>
            let applied : Term := apply_param_vars (Term.var sentinel (DebugName.named (inductive_bare_name ind))) params in
            solve_typevars scope applied (final_result_type expected_type) List.empty
    }

/// Does `t` still hold a reference that is a class method and nothing else
/// (`FromListLiteral.cons`, not its mangled `FromListLiteral_List_cons`)?
#[partial]
def mentions_class_method_ref (t : Term) (scope : Scope) (locals : LocalScope) : Bool :=
    match t {
        Term.var idx dbg =>
            if I64.beq idx sentinel then
                match dbg {
                    DebugName.named id => is_unresolved_class_method_ref id scope locals,
                    DebugName.unnamed => false,
                }
            else false,
        _ => any_mentions_class_method_ref (term_children t) scope locals,
    }

#[partial]
def any_mentions_class_method_ref (ts : List Term) (scope : Scope) (locals : LocalScope) : Bool :=
    match ts {
        List.empty => false,
        List.cons x rest =>
            if mentions_class_method_ref x scope locals then true
            else any_mentions_class_method_ref rest scope locals,
    }

def is_unresolved_class_method_ref (id : Identifier) (scope : Scope) (locals : LocalScope) : Bool :=
    match scope_resolve_name (NameRef.nid id) scope locals {
        ok _ => false,
        err _ =>
            if not (ref_names_class_method id scope) then false
            else
                match scope_find_class_def_for_ref id (match id { Identifier.id s => Identifier.id (last_dotted_segment s) }) scope {
                    ok _ => true,
                    err _ => false,
                },
    }

/// `t` with each free name that resolves to no type in `scope` (a signature
/// variable nothing solved) replaced by a hole.
#[partial]
def open_free_type_vars (t : Term) (scope : Scope) : Term :=
    match term_peel t {
        Term.var idx dbg =>
            if I64.beq idx sentinel then
                match dbg {
                    DebugName.named id => if is_scope_type_name id scope then t else Term.hole,
                    DebugName.unnamed => t,
                }
            else t,
        Term.app f a => Term.app (open_free_type_vars f scope) (open_free_type_vars a scope),
        Term.pi b dom cod => Term.pi b (open_free_type_vars dom scope) (open_free_type_vars cod scope),
        _ => t,
    }

/// `body_type_error`'s call-argument form: is this argument's inferred type
/// the parameter's type?
///
/// One definition for every application site, so the guards stay the same
/// as the def boundary's and a call-specific one can be added here alone.
/// `param` must already have THIS argument's own solutions applied
/// (`subst_typevars_term`/`subst_levels_term`): a raw declared parameter
/// still naming its signature variables is exactly the "no instantiation at
/// use sites" class `body_type_error`'s typevar guard skips, so comparing
/// the unsolved form would buy nothing.
///
/// `arg` is the SOURCE argument, not the elaborated one: `body_type_error`'s
/// hole test is what keeps an argument that still carries an inference hole
/// (an unannotated lambda, a do-bind continuation) out of the comparison.
def call_arg_type_error (arg : Term) (arg_typ : Term) (param : Term)
    (scope : Scope) (locals : LocalScope) : Option TypeError :=
    // REPORTING PASS ONLY. `scope.incomplete_match_ok` is the bit
    // `lang/module.mo`'s `scope_for_elab_body` sets on the ELABORATION path
    // (and what an explicit `#[allow_incomplete_match]` exemption sets on the
    // check path); `false` is the checked, reporting default. The comparison
    // must not run where its error is swallowed: `elaborate_def_with_scope`
    // keeps a rejected decl UN-elaborated for codegen, so a rejection here
    // removes a derive-generated method and the build fails stages later
    // with an unrelated name. MEASURED on `motes/weaver`: the whole-graph
    // elaboration resolves the bare `prefixed` in `std/src/derive.mo`'s
    // `beq_piece` to `motes/weaver`'s `prefixed : String -> TLine -> TLine`
    // (the open `whole-program-name-collisions.md` class), and the argument
    // check turned that latent collision into a failed build. `monad check`
    // still reports it -- a diagnostic belongs on the reporting path, the
    // same check-path-only split `elaborate_def_with_scope` already
    // documents for the def-body comparison.
    //
    // A DEPENDENT parameter (`fiber`'s `b : B`, still referencing the
    // earlier binders) cannot be compared with a closed argument type --
    // substituting the earlier arguments into it is work this checker does
    // not do, and comparing the raw index reports `expected A, found I64`
    // for a call the Rust host accepts.
    if scope.incomplete_match_ok
    then Option.none
    else if term_has_bound_var param
    then Option.none
    else if constructor_value_expected_as_function arg param scope
    then Option.none
    else body_type_error arg arg_typ param scope locals

/// Is `arg` a CONSTRUCTOR reference with at least one field being passed
/// where a FUNCTION is expected?
///
/// `type_check_con`/`type_check_free_var_con` type a constructor reference
/// as its owning inductive (`Map.fold` is a `Map K V`, not a function), so
/// a constructor passed as a FUNCTION VALUE compares as a bare type and is
/// reported as a mismatch: `map_parse UseFilter.use_items use_brace_items`
/// in `lang/src/parser.mo` is the live shape, rejected by the call-argument
/// check while the Rust host accepts it. Giving a constructor reference its
/// real Pi type is the "constructor-as-value typing" prerequisite recorded
/// in `implementations/checker-accepts-what-the-rust-host-rejects.md`, and
/// is out of scope here.
///
/// NULLARY constructors are deliberately NOT covered: a nullary constructor
/// genuinely IS its type, so `needs Msg.started` (`needs : (I64 -> Msg) ->
/// Msg`) is a real error and stays rejected -- that is the repro this whole
/// check exists for.
def constructor_value_expected_as_function (arg : Term) (param : Term) (scope : Scope) : Bool :=
    if Bool.not (is_pi_typ (term_peel param))
    then false
    else match constructor_ref_arity arg scope {
        Option.some fields => I64.gt fields 0,
        Option.none => false,
    }

/// The declared field count of the constructor `t` names, when `t` is a
/// bare or type-qualified constructor REFERENCE (never applied).
def constructor_ref_arity (t : Term) (scope : Scope) : Option I64 :=
    match term_peel t {
        Term.var idx dbg =>
            if I64.beq idx sentinel then
                match dbg {
                    DebugName.named id =>
                        let bare : Identifier := Identifier.id (last_dotted_segment (show_identifier id)) in
                        match scope_find_inductive_by_constructor (NamePath.mk (List.cons bare List.empty)) scope {
                            Option.some ind => constructor_arity_of ind bare,
                            Option.none => Option.none,
                        },
                    DebugName.unnamed => Option.none,
                }
            else Option.none,
        _ => Option.none,
    }

/// `def_call_check_args`'s per-argument tail: solve this parameter's
/// type variables from the argument's (already inferred) type, then
/// recurse for the remaining arguments.
#[partial]
def def_call_continue (arg : Term) (a_tt : TypedTerm) (param_ty : Term) (rest : List Term) (rest_params : List Term) (subst : List (Pair Identifier Term)) (levels : List (Pair Identifier SortLevel)) (scope : Scope) (local_types : List Term) (locals : LocalScope) : CallArgOutcome :=
    let a_typ : Term := a_tt.typ in
    let next_subst : List (Pair Identifier Term) := solve_typevars scope param_ty a_typ subst in
    // W1.4: the same argument pair also determines LEVEL variables, whose
    // solution cannot live in `subst` (a `SortLevel` is not a `Term`).
    // `solve_levels` is non-committal, so an argument that says nothing
    // about the level leaves it free for a later one to solve.
    let next_levels : List (Pair Identifier SortLevel) := solve_levels param_ty a_typ levels in
    // THE argument check: `try_type_check_def_call` used to check every
    // argument against `Term.hole` (see `check_arg_for_call`) and never
    // compare the result with the parameter, so `f "s"` for `f (x : I64)`
    // and `needs Msg.started` for `needs (f : I64 -> Msg)` checked
    // cleanly and reached codegen. The parameter is substituted FIRST:
    // `List A` solved from this argument becomes `List I64`, so a genuine
    // mismatch is reported against the type the caller actually wrote.
    let solved_param : Term := subst_levels_term (subst_typevars_term param_ty next_subst) next_levels in
    match call_arg_type_error arg a_typ solved_param scope locals {
        Option.some e => CallArgOutcome.call_args_type_error e,
        Option.none =>
    match def_call_check_args rest rest_params next_subst next_levels scope local_types locals {
        CallArgOutcome.call_args_decline => CallArgOutcome.call_args_decline,
        CallArgOutcome.call_args_type_error e => CallArgOutcome.call_args_type_error e,
        CallArgOutcome.call_args_ok pair =>
            match pair {
                DccPair.mk rest_elab rest_subst rest_levels =>
                    CallArgOutcome.call_args_ok (DccPair.mk (List.cons (a_tt.term) rest_elab) rest_subst rest_levels),
            },
    }
    }

/// A signature decomposed for `try_type_check_def_call`: its explicit
/// `Term.pi` chain's parameter types, and the final return type. Its
/// implicit type parameters need no separate field: a def's registered
/// `Def.typ` stores them as FREE vars (`Term.var sentinel ...`) -- the
/// parser leaves them free and `elaborate_def_typs` (`lang/module.mo`)
/// forall-wraps them only AFTER the scope (and its `def_sigs` entries)
/// is built -- and `solve_typevars` records every free-var match it
/// finds, no precomputed name set required.
pub struct SigInfo {
    params : List Term,
    ret : Term,
}

#[partial]
def sig_tvars_params_ret (sig : Term) : SigInfo :=
    sig_tvars_go sig 0 List.empty

/// Decompose the pi chain. Three-way at each binder, and all three
/// flavours really occur in a signature:
///
///   - an EXPLICIT binder is a value parameter: recorded in `params`.
///   - a QUANTIFIED type variable is OPENED with a fresh free placeholder
///     (`sig_tv_<n>`) via the standard open (`term_subst 0 placeholder
///     body`) -- so that even a sig whose type parameters arrive
///     bound (not this pipeline's usual already-free shape, see
///     `SigInfo`'s doc comment) still leaves them as free vars that
///     `solve_typevars` and `subst_typevars_term` can solve and rewrite.
///     `term_subst_go`'s fused shift also corrects the remaining indices
///     when the binder drops off.
///   - a LEVEL binder is DROPPED, for the reasons in the arm below.
///
/// Before R2b this was two arms, `Term.forall` and `Term.pi`, and the
/// three-way split lived inside the `forall` arm; the fold is what makes
/// the explicit case need its own branch rather than a catch-all.
#[partial]
def sig_tvars_go (t : Term) (n : I64) (params : List Term) : SigInfo :=
    match t {
        Term.pi b arg ret =>
            if binder_is_level b
            then
                // A LEVEL binder is not a type variable and must not be
                // opened with a term placeholder. Substituting `sig_tv_<n>`
                // for it would rename the binder while the `SortLevel.var u`
                // occurrences in the body keep the ORIGINAL name -- leaving
                // an unresolved level, which every comparison in
                // `lang/types.mo` answers `false` for, i.e. a spurious
                // rejection rather than an error anyone could read.
                //
                // A level binder carries no term-level index, so dropping it
                // outright (rather than substituting) is what keeps the body's
                // de Bruijn indices correct: `term_subst 0` is exactly the
                // shift that removing one binder requires, and the level
                // variables are name-keyed, so they need no shifting at all.
                sig_tvars_go (term_subst 0 (Term.sort (SortLevel.concrete 0)) ret) n params
            else if binder_is_explicit b
            then
                // An ordinary arrow: a real value parameter. It is not
                // opened -- there is no placeholder to make -- it is
                // recorded, and the walk continues down the chain.
                sig_tvars_go ret n (list_append params [arg])
            else
                // A quantified TYPE VARIABLE: open it with a fresh free
                // placeholder so `solve_typevars` and `subst_typevars_term`
                // can reach it.
                let fresh : Identifier := Identifier.id (String.concat "sig_tv_" (I64.to_string n)) in
                let placeholder : Term := Term.var sentinel (DebugName.named fresh) in
                sig_tvars_go (term_subst 0 placeholder ret) (n + 1) params,
        _ => { params := params, ret := t },
    }

/// Best-effort type-variable solver: structurally walk a callee's
/// declared parameter type against the argument's actual inferred
/// type, recording `name := actual_part` for every FREE `Term.var`
/// occurrence in the parameter type. Free vars in a registered
/// `Def.typ` are the def's implicit type parameters OR references to
/// global concrete types (see `SigInfo`'s doc comment) -- so recording
/// is additionally gated on the name NOT resolving in scope
/// (`is_scope_type_name` below): a concrete type name solved from a
/// mismatched actual would rewrite every later mention of it (the
/// same poisoning shape as the `Term.hole` case). The `sentinel` gate
/// also matters: a var BOUND by an enclosing binder inside the
/// parameter type must never be recorded.
/// Never fails -- a shape mismatch just stops collecting (the argument
/// was already checked successfully; this walk only recovers the
/// type-variable instantiation, it is not the correctness gate).
///
/// BOTH trees are peeled at the entry (R10), and each peel fixes a
/// different silent loss. A wrapper on the PARAMETER stops the walk at the
/// `_ => subst` arm, so a type variable simply never gets solved. A
/// wrapper on the ACTUAL does the same thing one level deeper -- and there
/// it also defeats the `Term.hole` guard above, which is the guard's whole
/// job: an actual this walk cannot see through is recorded as if it were
/// informative, and the poison the guard exists to prevent comes back
/// through a wrapper. Peeling cannot make the walk collect MORE than the
/// unwrapped term would, so this can only remove wrong answers.
#[partial]
def solve_typevars (scope : Scope) (param : Term) (actual : Term) (subst : List (Pair Identifier Term)) : List (Pair Identifier Term) :=
    let param_p : Term := term_peel param in
    let actual_p : Term := term_peel actual in
    match param_p {
        Term.var idx dbg =>
            if not (I64.beq idx sentinel) then subst
            else
                match dbg {
                    DebugName.named vid =>
                        // A `Term.hole` actual carries NO type information
                        // (an argument this infer-only checker couldn't
                        // type -- e.g. a constructor call whose own
                        // expected type bottomed out at hole). Recording
                        // it anyway poisons the substitution: EVERY free
                        // var in a pre-elaboration `Def.typ` has
                        // `idx == sentinel` (concrete type names like
                        // `ParamPair` included -- there is no `forall`
                        // wrapper distinguishing typevars from them at
                        // this point), so `List.cons (ParamPair.mk ...)
                        // List.empty` solved `ParamPair := Term.hole`
                        // from the hole-typed ctor arg and rewrote the
                        // monomorphic `List ParamPair` return into
                        // `(List _)` -- confirmed live via a minimal
                        // probe (match-arm shape only; the annotated
                        // top-level form masked it).
                        match actual_p {
                            Term.hole => subst,
                            // A free var that RESOLVES in scope is a
                            // concrete type name, not one of the def's
                            // implicit type parameters (those are never
                            // registered anywhere) -- and pre-elaboration
                            // `Def.typ` represents both identically, so
                            // resolution is the only discriminator. Not
                            // recording it keeps e.g. `def cp (x : P) :
                            // Box P`'s `P` unsolved when an argument
                            // infers to something else (the call is
                            // ill-typed; falling through unsolved
                            // degrades to the old lenient path rather
                            // than rewriting `Box P` into garbage).
                            _ =>
                                if is_scope_type_name vid scope then subst
                                else if subst_has_id subst vid then subst
                                else List.cons (Pair.pair vid actual) subst,
                        },
                    DebugName.unnamed => subst,
                },
        Term.pi p_b p_arg p_ret =>
            // A NON-EXPLICIT binder on the pattern side is not an
            // argument to match against, so it is stripped and the walk
            // continues -- exactly what the old `Term.forall` arm did.
            // Matching a former `forall` against a real `pi` argument
            // would solve a type variable from a value's type.
            if Bool.not (binder_is_explicit p_b)
            then solve_typevars scope p_ret actual_p subst
            else
                match actual_p {
                    // ...and the same on the ARGUMENT side: a
                    // quantified/level binder there is stripped and the
                    // pattern side is re-walked against its body.
                    Term.pi a_b a_arg a_ret =>
                        if binder_is_explicit a_b
                        then solve_typevars scope p_ret a_ret (solve_typevars scope p_arg a_arg subst)
                        else solve_typevars scope param a_ret subst,
                    _ => subst,
                },
        Term.app p_f p_a =>
            match actual_p {
                Term.app a_f a_a => solve_typevars scope p_f a_f (solve_typevars scope p_a a_a subst),
                _ => subst,
            },
        // `actual_p`, already peeled at the entry above: the peel sits at
        // ONE entry rather than at every helper's, so the tail helpers
        // below take their `actual` peeled by construction and carry no
        // unreachable peel of their own.
        Term.con p_con =>
            match p_con {
                Con.mk _name _typ_name _num_args p_args => con_solve_typevars scope p_args actual_p subst,
            },
        _ => subst,
    }

#[partial]
def con_solve_typevars (scope : Scope) (p_args : List (Option Term)) (actual : Term) (subst : List (Pair Identifier Term)) : List (Pair Identifier Term) :=
    match actual {
        Term.con a_con =>
            match a_con {
                Con.mk _name _typ_name _num_args a_args => con_args_solve_typevars scope p_args a_args subst,
            },
        _ => subst,
    }

#[partial]
def con_args_solve_typevars (scope : Scope) (p_args : List (Option Term)) (a_args : List (Option Term)) (subst : List (Pair Identifier Term)) : List (Pair Identifier Term) :=
    match p_args {
        List.empty => subst,
        List.cons p_opt p_rest =>
            match p_opt {
                Option.some p_t =>
                    match a_args {
                        List.empty => subst,
                        List.cons a_opt a_rest =>
                            match a_opt {
                                Option.some a_t => con_args_solve_typevars scope p_rest a_rest (solve_typevars scope p_t a_t subst),
                                Option.none => con_args_solve_typevars scope p_rest a_rest subst,
                            },
                    },
                Option.none =>
                    match a_args {
                        List.empty => subst,
                        List.cons _ a_rest => con_args_solve_typevars scope p_rest a_rest subst,
                    },
            },
    }

/// Does this identifier resolve to something in scope? Free vars in a
/// registered pre-elaboration `Def.typ` are EITHER the def's implicit
/// type parameters (never registered) OR references to global
/// concrete types (registered by `build_scope_*`), and both look like
/// `Term.var sentinel (DebugName.named ...)` -- so `solve_typevars`
/// uses this as its "is this really a type variable?" gate.
///
/// Item 5.1: a def-body annotation's bare type spelling (`Counter` in
/// `(c : Counter)`) is never alias-rewritten to its qualified form
/// (`resolve_open_alias_def`'s `typ` policy, mirrored for body lam
/// annotations), so in a qualified whole-program scope the def-table
/// lookup below misses for a name that IS a registered concrete type
/// -- its registration is `module::Name`. Retry the inductive table,
/// whose unique-suffix fallback (`scope_data_find_inductive`) accepts
/// the bare spelling when exactly one owner holds it. Ambiguous or
/// unknown names still classify as type variables, so the gate stays
/// conservative in the direction that only costs an ascription.
#[partial]
def is_scope_type_name (vid : Identifier) (scope : Scope) : Bool :=
    match scope_resolve_name (NameRef.nid vid) scope empty_locals {
        err _ =>
            match scope_find_inductive (NamePath.mk (List.cons vid List.empty)) scope {
                ok _ => true,
                err _ => false,
            },
        ok _ => true,
    }

/// Substitute a solved type-variable mapping (from `solve_typevars`)
/// throughout `t` -- reuses `name_subst_term` (`lang.typecheck.name_subst`)
/// per entry, whose own "free `Term.var sentinel (DebugName.named X)`"
/// target shape is exactly how a signature's implicit type parameter
/// appears in its parameter and return types (see `SigInfo`'s doc
/// comment above).
///
/// SIMULTANEOUS: a replacement is never rescanned by a later entry. With one
/// entry after another, `B := A` (the caller's own rigid `A`) followed by
/// `A := Unit` (the callee's `A`) rewrote the caller's `A` as well, and
/// `Monad.bind (ca rest) (fn _ => await_fiber f) : IO A` came back `IO Unit`.
#[partial]
def subst_typevars_term (t : Term) (subst : List (Pair Identifier Term)) : Term :=
    match subst {
        List.empty => t,
        List.cons entry rest =>
            match rest {
                List.empty =>
                    match entry {
                        Pair.pair vid replacement => name_subst_term vid replacement t,
                    },
                _ => release_typevars (stash_typevars t subst 0) subst 0,
            },
    }

def typevar_stash_ref (n : I64) : Term :=
    Term.var sentinel (DebugName.named (Identifier.id (String.concat "subst_tv_" (I64.to_string n))))

/// Phase 1 of `subst_typevars_term`: each solved variable becomes its own placeholder.
#[partial]
def stash_typevars (t : Term) (subst : List (Pair Identifier Term)) (n : I64) : Term :=
    match subst {
        List.empty => t,
        List.cons entry rest =>
            match entry {
                Pair.pair vid _ => stash_typevars (name_subst_term vid (typevar_stash_ref n) t) rest (n + 1),
            },
    }

/// Phase 2: each placeholder becomes its replacement, which no later step rescans.
#[partial]
def release_typevars (t : Term) (subst : List (Pair Identifier Term)) (n : I64) : Term :=
    match subst {
        List.empty => t,
        List.cons entry rest =>
            match entry {
                Pair.pair _ replacement => release_typevars (name_subst_term (Identifier.id (String.concat "subst_tv_" (I64.to_string n))) replacement t) rest (n + 1),
            },
    }

def subst_has_id (subst : List (Pair Identifier Term)) (target : Identifier) : Bool :=
    match subst {
        List.empty => false,
        List.cons entry rest =>
            match entry {
                Pair.pair vid _ => if id_eq vid target then true else subst_has_id rest target,
            },
    }

/// Rewrite a saturated application of a bound cubical primitive into the
/// `Term.cubical` it is: `ineg i0` checks, and is stored, as
/// `{ prim := ineg, args := [i0] }`. FIRST probe in `type_check_app`,
/// ahead of `try_type_check_def_call`, and the order is forced, not
/// stylistic: `def_sigs` holds the primitive's own declared signature
/// (`I -> I` for `ineg`, the prelude's `with Cubical` block), so the def-call probe
/// would type the call fine against it and the rewrite would silently
/// never happen -- the term would stay `Term.app (var ineg) i0`,
/// invisible to every cubical rule downstream.
///
/// `Option.none` whenever the spine is not a cubical call this checker
/// can own outright: head not a sentinel free var, a LOCAL shadowing the
/// name (same guard and same reason as `try_type_check_def_call`), no
/// registered primitive under the resolved name, or the spine
/// UNDER-applied against `cubical_arity` -- a partially applied `imeet i`
/// falls through to the def-call probe, whose declared signature is the
/// right type for exactly that case. OVER-application falls through too
/// (a saturated primitive can be applied to more later -- at Stage 2, a
/// path applied to an endpoint), so the arity test is equality, not
/// `<=`. Everything else is handed to `type_check_cubical`, which checks
/// each argument against `I` and unifies the primitive's result type
/// against the expected one. `#[terminating]` (like `type_check_app`,
/// its caller): the probe itself makes one call and never recurses, but
/// it sits inside the checker cycle, and this is the attribute the
/// cycle's members carry.
#[terminating]
def try_type_check_cubical_call (app_term : Term) (expected_type : Term) (scope : Scope)
    (local_types : List Term) (locals : LocalScope) : Option (Result TypeError TypedTerm) :=
    match flatten_call_spine app_term {
        CallSpine.mk head args =>
            match head {
                Term.var idx dbg =>
                    match dbg {
                        DebugName.named id =>
                            if not (I64.beq idx sentinel) then Option.none
                            else if is_some_local (scope_find_local id locals) then Option.none
                            else
                                match scope_resolve_name (NameRef.nid id) scope locals {
                                    err _ => Option.none,
                                    ok sd =>
                                        match sd {
                                            mk resolved_name _ _ _ _ =>
                                                match scope_find_cubical_prim resolved_name scope {
                                                    Option.none => Option.none,
                                                    Option.some prim =>
                                                        let saturated : Bool :=
                                                            I64.beq (List.length args) (cubical_arity prim) in
                                                        if Bool.not saturated then Option.none
                                                        else
                                                            let c : Cubical := { prim := prim, args := args } in
                                                            Option.some
                                                                (type_check_cubical c expected_type scope
                                                                    local_types locals),
                                                },
                                        },
                                },
                        DebugName.unnamed => Option.none,
                    },
                _ => Option.none,
            },
    }

// `#[terminating]`: `type_check_app_ordinary` is this function's own
// factored-out tail (see its doc comment), not a recursive descent --
// it consumes the ALREADY-CHECKED `a_tt` and never re-enters
// `type_check_app` with the same arguments, so the pair terminates
// exactly as the single fused function did before the split.
#[terminating]
def type_check_app (f : Term) (a : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match dict_hint_name a {
        // `f #Named.Instance` -- the marker arm. Everything else is the
        // pre-existing body, untouched.
        Option.some hint => try_type_check_hinted_app f hint expected_type scope local_types locals,
        Option.none =>
    match try_type_check_cubical_call (Term.app f a) expected_type scope local_types locals {
        Option.some r => r,
        Option.none =>
    match try_type_check_def_call (Term.app f a) expected_type scope local_types locals {
        Option.some r => r,
        Option.none =>
    match try_type_check_con_call (Term.app f a) expected_type scope local_types locals {
        Option.some r => r,
        Option.none =>
    match infer_position_hole f a {
        Option.some e => err e,
        Option.none =>
    let a_expected : Term := app_arg_expected_type_from_callee f a expected_type scope local_types locals in
    match type_check a a_expected scope local_types locals {
        ok a_tt0 =>
            let a_tt : TypedTerm := recheck_against_callee_domain f a a_tt0 a_expected expected_type scope local_types locals in
            if not (struct_literal_arg_matches_expected a a_expected scope) then
                // The argument's ordinary check SUCCEEDED, but only
                // vacuously -- see `struct_literal_arg_matches_expected`.
                // Treat it as not applying, so the named-call spread
                // below gets its chance, exactly as the reference does
                // (`core_check.rs`, `Ok(()) if struct_literal_arg_
                // matches_expected(..)`).
                match named_call_fields_of a {
                    Option.none => type_check_app_ordinary a_tt f expected_type scope local_types locals,
                    Option.some fields =>
                        match type_check_named_call f fields expected_type scope local_types locals {
                            err e2 => err e2,
                            ok result => match result {
                                Option.some tt => ok tt,
                                Option.none => type_check_app_ordinary a_tt f expected_type scope local_types locals,
                            },
                        }
                }
            else
            type_check_app_ordinary a_tt f expected_type scope local_types locals,
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
    }
    }
    }
    }
    }

/// The `f #Named.Instance` arm of `type_check_app` (below). The hint
/// marker lowers to the INNERMOST application's argument, so this is
/// reached at `(f #Hint)` -- for an ordinary resolvable def call the
/// outer spine's `try_type_check_def_call` already peeled, validated and
/// re-attached the marker, so what reaches here is chiefly the
/// class-method shape (whose callee does not resolve as a def at all).
/// A class-method callee dispatches THROUGH the hinted instance
/// directly (mirroring `resolve_class_method_carrier`, so the
/// elaborated term carries the hinted instance's mangled method and the
/// codegen pass never re-does the choice); any other callee is checked
/// alone with the marker re-attached, leaving the dispatch to the
/// codegen dict pass.
def try_type_check_hinted_app (f : Term) (hint : String) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match term_peel f {
        Term.var idx dbg =>
            match dbg {
                DebugName.named id =>
                    let classes : List Class := scope_data_classes (scope_globals scope) in
                    // The class whose method `id` is: the dotted spelling
                    // (`Ord.compare`) through `class_method_ref`, the bare
                    // one (`compare`) through the class-def registry the
                    // free-var path's own `resolve_class_method` arm uses
                    // -- a bare name never reaches `class_method_ref`'s
                    // prefix rule, so without the second lookup every
                    // bare class-method hint would fall to the
                    // constrained-def arm and die on `unknown variable`.
                    let owner : Option (Pair NamePath Identifier) :=
                        match class_method_ref classes id {
                            Option.some ref =>
                                match ref {
                                    ClassMethodRef.mk cls method_name =>
                                        match cls {
                                            Class.mk cname _ _ _ _ =>
                                                Option.some (Pair.pair (NamePath.mk (List.cons cname List.empty)) method_name),
                                        },
                                },
                            Option.none =>
                                match id {
                                    Identifier.id s =>
                                        match dotted_qualifier s {
                                            Option.some _ => Option.none,
                                            Option.none =>
                                                match scope_find_class_def_by_name id scope {
                                                    ok cd =>
                                                        match cd {
                                                            mk cls_name _ method_name _ => Option.some (Pair.pair cls_name method_name),
                                                        },
                                                    err _ => Option.none,
                                                },
                                        },
                                },
                        } in
                    match owner {
                        Option.some owner_pair =>
                            match owner_pair {
                                Pair.pair owner_cls method_name =>
                            let one_hint : List String := List.cons hint List.empty in
                            match scope_find_instance_by_name scope hint {
                                Option.none => err (TypeError.custom (String.concat "no instance named '" (String.concat hint "'"))),
                                Option.some ins =>
                                    match ins {
                                        Instance.mk insname ins_cls _ ins_args _ _ _ =>
                                            if not (class_name_eq ins_cls owner_cls)
                                            then err (TypeError.custom (String.concat "instance '" (String.concat hint (String.concat "' is not an instance of the class owning '" (String.concat (show_identifier id) "'")))))
                                            else
                                                // The carrier the call's own expectation
                                                // reveals; the instance's first declared
                                                // arg when it reveals nothing, so a
                                                // concrete hinted instance dispatches
                                                // with no evidence at all (the same
                                                // fallback lang.scope's dict pass uses).
                                                let hint_carrier : Term :=
                                                    match carrier_from_expected_type expected_type {
                                                        Option.some c => c,
                                                        Option.none =>
                                                            match ins_args {
                                                                List.cons a _ => a,
                                                                List.empty => Term.hole,
                                                            },
                                                    } in
                                                let bindings : List (Pair Identifier Term) :=
                                                    carrier_bindings (instance_wildcard_names ins) ins_args hint_carrier in
                                                resolve_class_method_d4 insname ins_cls method_name (emitted_dict_constraints (scope_data_constrained_def_classes (scope_globals scope)) (scope_data_classes (scope_globals scope)) ins method_name) ins_args hint_carrier bindings expected_type scope locals,
                                    },
                            },
                            },
                        Option.none =>
                            // Not a class-method callee: validate the hint against
                            // the callee's own registered constraints when the callee
                            // resolves, then check the callee alone, marker re-attached.
                            match scope_resolve_name (NameRef.nid id) scope locals {
                                err _ => err (TypeError.unknown_var (NameRef.nid id)),
                                ok sd =>
                                    match sd {
                                        mk resolved_name _ _ _ _ =>
                                            let one_hint : List String := List.cons hint List.empty in
                                            match validate_dict_hints id (Option.some resolved_name) one_hint scope {
                                                Option.some e => err e,
                                                Option.none =>
                                                    match type_check f expected_type scope local_types locals {
                                                        err e => err e,
                                                        ok tt =>
                                                            ok (mk_typed (rebuild_call tt.term (dict_hint_marker_terms one_hint)) tt.typ),
                                                    },
                                            },
                                    },
                            },
                    },
                DebugName.unnamed => err (TypeError.custom "dict hint on an unnamed callee"),
            },
        _ => err (TypeError.custom "dict hint on a non-variable callee"),
    }

/// The reference checker's `App(Lam{param_typ: Hole}, arg)` arms --
/// `check`'s at `core/src/core_check.rs:1582-1593` (the `matches!` is
/// `:1587`), `infer`'s twin at `:946-964` -- do not CHECK their argument
/// against the unannotated parameter's type; they INFER it, and `infer` on
/// a hole is `InferError::CannotInferHole` (`:884`), rendered "cannot infer
/// the type of a hole; add a type annotation" (`core_check_module.rs:1829-
/// 1831`). Every other application reaches the generic arm, which
/// `expect_pi`s and then CHECKs -- and a check *against* a hole succeeds,
/// both directions pinned by the reference's own
/// `test_infer_hole_errors_but_check_hole_succeeds` (`core_check.rs:3817`).
///
/// Self-hosted there is no separate `infer`: `type_check a Term.hole` IS
/// the infer mode, and `Term.hole => ok (mk_typed expected_type
/// expected_type)` (`type_check`, above) accepts anything, holes included.
/// So this arm's observable content here is exactly a hole ARGUMENT whose
/// callee is a literal, hole-annotated lambda -- which is also what that
/// argument's expected type already was (`app_arg_expected_type` above), so
/// the two spellings coincide at this one site and nothing else has to
/// change.
///
/// The callee test is syntactic because the reference's own is
/// (`matches!(fun.strip_ctx(), Lam{param_typ, ..} if matches!(param_typ
/// .strip_ctx(), Hole))`) -- and that syntactic width is load-bearing
/// rather than incidental, which is what three earlier candidate rules
/// each got wrong. `(fn x => fn y => x) 1 _` must stay ACCEPTED: there the
/// OUTER callee is an application, not a lambda, so it reaches the generic
/// `check(arg, Hole)` path exactly as the reference documents. A rule that
/// instead rejected every hole argument reaching the uninformative
/// `app_arg_expected_type` DEFAULT arm would reject that probe; a rule keyed
/// on "the callee's parameter is a declared `_`" fails on `(fn (x : _) =>
/// x) _`, which the reference rejects exactly like the unannotated form,
/// because a written `_` and an absent annotation are the same construct
/// there.
///
/// `term_peel` on each of the three terms mirrors the reference's own
/// `strip_ctx()` (`core/src/core_term.rs:393`) at the same positions;
/// without it a located hole would silently stop matching.
///
/// This arm is only HALF the port, and the other half is in the parser:
/// the reference's bare-name lambda param IS `param(i, Hole)`
/// (`core/src/parser.rs:464-466`), while the port's `build_nested_lambdas`
/// wrote a SORT there -- the port's marker for an OMITTED KIND at its
/// three type-binder sites (`:1372`/`:1423`/`:2667`). That was not a
/// spelling mix-up; it was an assertion of a type no source had said.
/// Written onto a value's parameter it made the `param_typ` test above
/// false for `fn x => x`, so the arm fired only for a written `_` and
/// `(fn x => x) _` stayed accepted, with no source able to explain why.
/// The assertion was visible from the other side too: `app_arg_expected_type`
/// hands a lam's `param_typ` to its ARGUMENT as the expected type, so
/// `(fn x => x) arg` was checking `arg` against a sort. Both halves are
/// needed and neither is sufficient, and the repair belongs in the producer
/// -- the guard's premise was true of the reference and false of the port,
/// so the value had to be made to match rather than a predicate taught which
/// wrong value to tolerate. `type T {}`-based rows for the accepted half,
/// and the two rejected rows, are pinned in `lang/src/module.mo`'s
/// hole-in-infer-position tests.
#[partial]
def infer_position_hole (f : Term) (a : Term) : Option TypeError :=
    match term_peel f {
        Term.lam _dbg param_typ _body =>
            if is_hole (term_peel param_typ) && is_hole (term_peel a)
            then Option.some (TypeError.custom "cannot infer the type of a hole; add a type annotation")
            else Option.none,
        _ => Option.none,
    }

/// The ordinary (non-named-call) continuation of `type_check_app` once
/// the argument has been checked: check `f` against the Pi built from
/// the argument's own inferred type, then extract the result. Factored
/// out of `type_check_app`'s own body so BOTH its success paths -- the
/// plain one, and the one reached after a vacuously-checking struct
/// literal declined to become a named call -- share it verbatim
/// instead of duplicating the sequence.
def type_check_app_ordinary (a_tt : TypedTerm) (f : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
            let a_term : Term := a_tt.term in
            let a_typ : Term := a_tt.typ in
            let f_expected : Term := Term.pi binder_anon a_typ expected_type in
            match type_check f f_expected scope local_types locals {
                ok f_tt =>
                    let f_term : Term := f_tt.term in
                    let f_typ : Term := f_tt.typ in
                    match callee_domain_error f a_term a_typ f_typ scope locals {
                        Option.some e => err e,
                        Option.none =>
                    extract_pi_ret f_term a_term f_typ a_typ expected_type scope local_types locals,
                    },
                err e => err e,
            }

/// The ordinary path's argument check: the callee's own Pi domain against
/// the argument's inferred type.
///
/// Only this path sees a LOCAL function value. A def call resolves through
/// `try_type_check_def_call` (which checks each argument itself) and never
/// reaches here, and a class method's carrier is derived FROM the argument
/// (`carrier_from_expected_type`), so its domain is the argument's own type
/// by construction and compares equal. What is left is exactly the shape
/// the def probe declines on: `def danger (pick : String -> I64) : I64 :=
/// pick 1i64`, accepted at HEAD and rejected by the Rust host.
///
/// `pi_domain_of` declines a hole domain and a folded `forall` -- the
/// callee knows no more than we do there; `call_arg_type_error` owns the
/// rest of the guards.
///
/// A CLASS-METHOD callee is skipped outright. Its carrier is derived FROM
/// the argument's own inferred type (`carrier_from_expected_type`), so the
/// Pi this path inspects is synthesized out of the very type it would be
/// compared with -- and for a do-block over a monad transformer the
/// derivation can apply the carrier once more than the source did, which is
/// exactly the disagreement the comparison then reports: MEASURED on
/// `motes/oak/src/tests/html_t_tests.mo`'s `prog_do_open`, where the
/// argument typed `HtmlT (HtmlT RenderM Open Open) Open Open Unit` and the
/// derived domain `HtmlT RenderM Open Open Unit`. The Rust host accepts it.
def callee_domain_error (f : Term) (a_term : Term) (a_typ : Term) (f_typ : Term)
    (scope : Scope) (locals : LocalScope) : Option TypeError :=
    if callee_is_class_method f scope
    then Option.none
    else match pi_domain_of f_typ {
        Option.none => Option.none,
        Option.some dom => call_arg_type_error a_term a_typ dom scope locals,
    }

/// Does `f`'s call spine name a CLASS METHOD (a method declared by a class,
/// whose carrier the checker resolves per call)?
def callee_is_class_method (f : Term) (scope : Scope) : Bool :=
    match flatten_call_spine f {
        CallSpine.mk head _args =>
            match class_method_declared_sig head scope {
                Option.some _ => true,
                Option.none => false,
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

// --- An unannotated lambda argument's parameter type (see the bug plan
// `implementations/do-bind-binder-untyped.md`).
//
// `let x <- e;` desugars (`lang/src/parser/lower_parse.mo`) to
// `Term.app (Term.app <Monad.bind> e) (Term.lam (named x) Term.hole <rest>)`
// -- an argument that is a lambda whose WRITTEN param type is a hole, handed
// to a callee that is not an inline lambda (`Monad.bind e`). Both conditions
// defeat `app_arg_expected_type` above, so the lambda reaches
// `type_check_lam`'s `_` arm (branch B), which stores the written hole as the
// binder's type; `Term.hole` is a matches-anything wildcard here, never a
// solvable meta (`lang/src/typecheck/whnf.mo`), so nothing downstream recovers
// it and the first field read or `{ .. }` through the binder fails with
// "cannot resolve `{ .. }`: the matched value's type isn't known here".
//
// The type is not MISSING, only late: the callee's domain is exactly what the
// lambda needs. Recovering it here rather than reordering `type_check_app`
// (callee before argument, as `core/src/core_check.rs`'s App arm does) is
// deliberate: `resolve_class_method` derives a class method's carrier from the
// Pi that `type_check_app_ordinary` synthesizes FROM THE ARGUMENT'S ALREADY
// INFERRED TYPE (`carrier_from_expected_type`, stated in that pair's own doc
// comments), so inferring the callee first would break carrier derivation for
// every class method. This is additive instead -- it changes the argument's
// expected type only for the shape above, and `Term.hole` otherwise.
//
// A discovered domain is handed over ONLY when it is a real, CLOSED type --
// no name left in it that resolves to nothing, and no name the callee's own
// declaration binds. That gate is not caution, it is the whole difference
// between this fix and a regression: a signature variable that nothing solved
// is a type variable, and a binder carrying one re-creates the failure
// `class_method_var_names` (`lang/src/scope.mo`) and `lam_binder_type` exist
// to prevent -- measured there on `init/src/foldable_tests.mo`'s `Foldable.
// foldr (fn x acc => x + acc) 0 [1, 2, 3]`, whose `+` then resolved against
// the wildcard-headed `instance [Add A] HAdd A A A`, emitting a dictionary
// that called itself until the driver died by signal (`driver exited -1`).
// Handing the lambda the callee's own abstract domain is, without the gate,
// exactly that bug re-entered from the checker side.

/// A callee's domain at the argument position we are about to check, together
/// with the names the callee's own declaration binds.
///
/// The names travel with the domain because they ARE the test that decides
/// whether the domain may be handed to a lambda (see `lam_binder_hint`), and
/// which names are variables depends on where the declaration came from and
/// not on its shape at all -- the same point `sig_hints` makes for the
/// resolution pass's identical hint, whose `names` parameter exists for the
/// same reason.
pub struct CalleeDomain {
    dom : Term,
    vars : List Identifier,
}

/// The type to check an application's ARGUMENT against. `app_arg_expected_type`
/// handles the inline-lambda callee; this adds the one other shape whose
/// answer is knowably useless -- an unannotated lambda argument to a non-lambda
/// callee, i.e. a do-bind's continuation -- by asking the callee for its domain
/// at this position. For a class-method callee, the carrier the call's expected
/// result implies is also handed down (to the argument, and to a continuation's
/// body). Every other argument keeps the old hole unchanged.
#[terminating]
def app_arg_expected_type_from_callee (f : Term) (a : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Term :=
    let written : Term := app_arg_expected_type f in
    if is_hole written && arg_is_unannotated_lam a then
        match callee_arg_domain f expected_type scope local_types locals {
            Option.none => written,
            Option.some cd =>
                match lam_binder_hint cd scope {
                    Option.some bt => Term.pi binder_anon bt (class_method_lam_body_expected f expected_type cd scope),
                    Option.none =>
                        let body : Term := class_method_lam_body_chain_expect f expected_type cd scope in
                        if is_hole body then written else Term.pi binder_anon Term.hole body,
                },
        }
    else if is_hole written then
        match class_method_result_domain f expected_type scope local_types locals {
            Option.some d => d,
            Option.none => written,
        }
    else
        written

/// A class-method call's declared type variables, solved from the call's
/// own EXPECTED result: the parameter the next argument fills, the names the
/// class binds, and what `ret` matched against the expected result type.
/// Cheap by construction -- it checks no argument.
struct ResultSolution {
    next_param : Term,
    vars : List Identifier,
    subst : List (Pair Identifier Term),
}

#[partial]
def class_method_result_solution (f : Term) (expected : Term) (scope : Scope) : Option ResultSolution :=
    match flatten_call_spine f {
        CallSpine.mk head args =>
            match class_method_declared_sig head scope {
                Option.none => Option.none,
                Option.some decl =>
                    match sig_tvars_params_ret decl.sig {
                        SigInfo.mk params ret =>
                            if is_bare_type_var ret then Option.none else
                            match nth_type (List.length args) params {
                                Option.none => Option.none,
                                Option.some next_param =>
                                    let sol : ResultSolution := { next_param := next_param, vars := decl.vars, subst := solve_typevars scope ret (final_result_type expected) List.empty } in
                                    Option.some sol,
                            },
                    },
            },
    }

/// A bare-variable result (`put : A -> A`) says nothing the arguments do not,
/// and an ill-typed expectation would pin it.
def is_bare_type_var (t : Term) : Bool :=
    match term_peel t {
        Term.var _ _ => true,
        _ => false,
    }

/// `t` with each of `vars` still free in it replaced by a hole: an unsolved
/// signature variable says "unknown here", not a type to check against.
#[partial]
def fill_unsolved_vars (vars : List Identifier) (t : Term) : Term :=
    match vars {
        List.empty => t,
        List.cons v rest => fill_unsolved_vars rest (name_subst_term v Term.hole t),
    }

/// An applied type whose head survived the hole-fill: `IO _` carries the
/// carrier, `_ _` and a bare `_` carry nothing.
#[partial]
def has_informative_head (t : Term) : Bool :=
    match term_peel t {
        Term.hole => false,
        Term.app g _ => has_informative_head g,
        _ => true,
    }

/// What a class-method call's NON-lambda argument should be checked against
/// when the carrier is only known from the call's expected result: the
/// declared parameter type with the carrier solved and the rest left open.
/// `Monad.bind (Monad.pure c) k : IO I64` hands `Monad.pure c` the type
/// `IO _`, which is what lets the inner call resolve its own carrier.
#[partial]
def class_method_result_domain (f : Term) (expected : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Option Term :=
    match class_method_result_solution f expected scope {
        Option.some sol =>
            match sol.subst {
                List.cons _ _ =>
                    let d : Term := fill_unsolved_vars sol.vars (subst_typevars_term sol.next_param sol.subst) in
                    if has_informative_head d then Option.some d else class_method_chain_domain f expected scope local_types locals,
                List.empty => class_method_chain_domain f expected scope local_types locals,
            },
        Option.none => class_method_chain_domain f expected scope local_types locals,
    }

/// The argument's declared parameter type with what the call's LATER
/// arguments -- the rest of the expected Pi chain -- fix substituted in
/// (`class_method_next_param`'s domain, the lambda-hint channel's own
/// source). `BEq.beq Bounded.max_bound gt` is the motivating shape: the
/// zero-argument class call is the FIRST argument, so its own expectation
/// is a hole, and only `gt`'s `Ordering` names the instance it means.
/// Refused when the domain still holds an unresolvable name or one of the
/// method's own unsolved variables -- an argument checked against those
/// would resolve against the wrong instance, exactly what `lam_binder_hint`
/// refuses to hand a lambda.
#[partial]
def class_method_chain_domain (f : Term) (expected : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Option Term :=
    match class_method_next_param f expected scope local_types locals {
        Option.none => Option.none,
        Option.some cd =>
            if has_informative_head cd.dom
                && Bool.not (mentions_unresolved_name cd.dom scope)
                && Bool.not (type_mentions_any cd.vars cd.dom)
            then Option.some cd.dom
            else Option.none,
    }

/// The expected type of an unannotated continuation's BODY: the domain's
/// codomain with the result-derived carrier filled in and the rest left open
/// (`A -> M B` against `IO I64` gives `IO _`). `Term.hole` when that says
/// nothing -- the old behavior.
#[partial]
def class_method_lam_body_expected (f : Term) (expected : Term) (cd : CalleeDomain) (scope : Scope) : Term :=
    match term_peel cd.dom {
        Term.pi _ _ cod =>
            match class_method_result_solution f expected scope {
                Option.none => Term.hole,
                Option.some sol =>
                    let filled : Term := fill_unsolved_vars cd.vars (subst_typevars_term cod sol.subst) in
                    if has_informative_head filled then filled else Term.hole,
            },
        _ => Term.hole,
    }

/// `class_method_lam_body_expected` for a lambda whose BINDER the hint gate
/// refused (`app_arg_expected_type_from_callee`'s `Option.none` arm): the
/// chain-solved domain's codomain still applies -- `class_method_next_param`
/// already substituted what the call's LATER arguments fix, so
/// `Foldable.foldr (fn x acc => x + acc) 0 t` keeps `acc : I64` and `I64` as
/// the body's result, which is what resolves its `HAdd.add`. With the binder
/// unknown this codomain is the body's only expectation; the retired pass
/// read the same one (`sig_arg_hints`). Refused, falling back to the
/// result-only answer, when it still names something unresolved or one of
/// the method's own unsolved variables.
#[partial]
def class_method_lam_body_chain_expect (f : Term) (expected : Term) (cd : CalleeDomain) (scope : Scope) : Term :=
    match term_peel cd.dom {
        Term.pi _ _ cod =>
            if has_informative_head cod
                && Bool.not (mentions_unresolved_name cod scope)
                && Bool.not (type_mentions_any cd.vars cod)
            then cod
            else class_method_lam_body_expected f expected cd scope,
        _ => class_method_lam_body_expected f expected cd scope,
    }

/// Is this argument a lambda whose written parameter type is a hole? Peeled,
/// matching `infer_position_hole`'s own peeling, so a wrapped lambda still
/// counts.
def arg_is_unannotated_lam (a : Term) : Bool :=
    match term_peel a {
        Term.lam _dbg param_typ _body => is_hole (term_peel param_typ),
        _ => false,
    }

/// The binder type an unannotated lambda argument should learn from its
/// callee, or `Option.none` when the callee's domain is not usable as one.
///
/// Only the DOMAIN is asserted, never the codomain -- the caller builds
/// `Term.pi bt Term.hole`, not the callee's Pi verbatim. The lambda's real
/// expected type is `Term.pi dom ret`, and handing that over whole would make
/// `type_check_lam`'s branch A check the continuation's body against a `ret`
/// like `IO B` whose `B` is an unsolved free variable; with no metas there is
/// nothing to solve it against, so every do-bind in the corpus would fail on a
/// variable the checker cannot solve. The binder's type is what this bug is
/// about, and it is what gets enforced.
///
/// Three rejections, in order of what they protect:
///
///  * an uninformative binder type (hole or sort) says nothing, so it is no
///    better than the written hole -- the parser writes a sort for an omitted
///    annotation, and `is_uninformative_carrier` is this module's own test
///    for both shapes;
///  * a free name that resolves to no type in `scope` is a TYPE VARIABLE the
///    callee's declaration never solved (`B` in `Monad.bind`'s `A -> M B`,
///    which nothing in the call site can bind -- the result position is not
///    reachable from here). Handing one down is the foldable regression;
///  * a name the callee's OWN declaration binds, even one that happens to
///    resolve as a type, because a class parameter's name is a variable to
///    the call site however the scope reads it. `class_method_var_names`
///    reports that set, and `hint_arrow_domain` (`lang/src/scope.mo`) applies
///    the identical rule before its own hint goes down.
#[partial]
pub def lam_binder_hint (cd : CalleeDomain) (scope : Scope) : Option Term :=
    let bt : Term := binder_typ_of cd.dom in
    if is_uninformative_carrier (term_peel bt) then Option.none
    else if mentions_unresolved_name bt scope then Option.none
    else if type_mentions_any cd.vars bt then Option.none
    else Option.some bt

/// The type a lambda's parameter would take from this domain: the domain of
/// the domain, for a function-typed one (`Monad.bind`'s continuation parameter
/// is `A -> M B`, and the lambda's own binder is its `A`).
def binder_typ_of (dom : Term) : Term :=
    match term_peel dom {
        Term.pi _ binder_typ _ret => binder_typ,
        _ => dom,
    }

/// Does `t` mention a free name that resolves to no type in `scope`?
///
/// `type_mentions_any`'s sibling with the name set left out, for the one
/// caller that cannot supply one: the names it must reject are exactly those
/// that resolve to nothing, so resolution IS the test. The `sentinel` gate is
/// `solve_typevars`'s own -- a var bound by a binder inside `t` carries a real
/// de Bruijn index and is not free, so it is not a signature variable.
#[partial]
def mentions_unresolved_name (t : Term) (scope : Scope) : Bool :=
    match term_peel t {
        Term.var idx dbg =>
            if I64.beq idx sentinel then
                match dbg {
                    DebugName.named id => Bool.not (is_scope_type_name id scope),
                    DebugName.unnamed => false,
                }
            else
                false,
        Term.app f a => if mentions_unresolved_name f scope then true else mentions_unresolved_name a scope,
        // Both children, and the domain is inert. A former `forall`'s kind
        // was skipped -- it is a `Term.sort` or a bare type variable, and
        // walking it changes nothing that the old arm could see: the
        // domain of a folded `forall` is always a sort, which answers
        // `false` below.
        Term.pi _b dom cod => if mentions_unresolved_name dom scope then true else mentions_unresolved_name cod scope,
        Term.lam _dbg ty body => if mentions_unresolved_name ty scope then true else mentions_unresolved_name body scope,
        _ => false,
    }

/// The domain a callee expects at the position of an argument we are about to
/// check. Two sources, cheapest first.
#[terminating]
def callee_arg_domain (f : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Option CalleeDomain :=
    // A class method first: its own inference yields the class's ABSTRACT
    // signature (a hole at this position) rather than an instance-solved Pi,
    // so the declared signature in the class is the only source that has an
    // answer -- and consulting it first also spares a do-bind the wasted
    // `type_check` below.
    match class_method_next_param f expected_type scope local_types locals {
        Option.some cd => Option.some cd,
        Option.none => inferred_callee_domain f scope local_types locals,
    }

/// The domain of the callee's own inferred type, for callees that are not
/// class methods (a parameter bound to a function, say).
///
/// No `vars`: the callee is an ordinary term, not a class declaration, so
/// there is no declared binder set to read. `lam_binder_hint`'s resolution
/// test is what carries this path -- and it is the stronger of the two, since
/// an unresolved name is rejected whether or not a declaration owns it.
#[terminating]
def inferred_callee_domain (f : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Option CalleeDomain :=
    match type_check f Term.hole scope local_types locals {
        err _ => Option.none,
        ok f_tt =>
            match pi_domain_of f_tt.typ {
                Option.none => Option.none,
                Option.some dom => Option.some (CalleeDomain.mk dom List.empty),
            },
    }

/// Peel a (possibly binder-wrapped) Pi chain down to its first value domain,
/// if that domain carries real information. A hole domain means the callee
/// knows no more than we do, which is `Option.none` so the caller keeps its
/// hole.
///
/// `binder_is_explicit` is what keeps a folded `forall` out of the answer.
/// Its `dom` is `Term.sort (SortLevel.concrete 0)` or `... 1` -- a real
/// `Option.some`, not a hole, so without the guard a quantified type
/// variable's KIND would be returned as the domain the next argument has to
/// have. Before R2b the two were different constructors and the strip arm
/// caught it for free.
#[partial]
def pi_domain_of (t : Term) : Option Term :=
    match term_peel t {
        Term.pi b dom ret =>
            if binder_is_explicit b
            then if is_hole (term_peel dom) then Option.none else Option.some dom
            else pi_domain_of ret,
        _ => Option.none,
    }

/// The parameter a CLASS METHOD declared for the argument position `f`'s spine
/// has reached, with the method's type variables solved against the arguments
/// already applied -- the domain the next argument must have.
///
/// Reads the class's own declared method signature (`class Monad` declares
/// `bind (a : M A) (f : A -> M B) : M B`), split by `sig_tvars_params_ret` and
/// solved with the same `def_call_check_args` the signature-driven def path
/// uses, so `A` and `B` come out as the real types the call site implies
/// rather than the free variables the registry signature stores.
///
/// Solving is best-effort by construction (`def_call_check_args`'s own doc
/// comment: an argument this infer-only checker cannot type leaves its
/// variables unsolved), which is why the result carries the class's variable
/// names alongside the domain -- see `CalleeDomain`.
#[terminating]
def class_method_next_param (f : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Option CalleeDomain :=
    match flatten_call_spine f {
        CallSpine.mk head args =>
            match class_method_declared_sig head scope {
                Option.none => Option.none,
                Option.some decl =>
                    match sig_tvars_params_ret decl.sig {
                        SigInfo.mk params ret =>
                            // The NEXT parameter is the one after as many
                            // arguments as the spine has already applied.
                            match nth_type (List.length args) params {
                                Option.none => Option.none,
                                Option.some next_param =>
                                    // `dcc.levels` is not read here: a
                                    // level-polymorphic CLASS method is
                                    // out of W1.4's scope (see
                                    // `solve_levels`'s own doc comment).
                                    // Both failure kinds collapse to `none`:
                                    // this path produces a HINT for an
                                    // argument's binder, never a diagnostic.
                                    // The call's own check reports.
                                    match def_call_check_args args params List.empty List.empty scope local_types locals {
                                        CallArgOutcome.call_args_decline => Option.none,
                                        CallArgOutcome.call_args_type_error _ => Option.none,
                                        CallArgOutcome.call_args_ok dcc =>
                                            // `dcc.subst` solves type variables from arguments
                                            // ALREADY applied; a HOF argument whose carrier
                                            // comes from a LATER sibling (`Comonad.extend (fn a
                                            // => ...) (Id.id 41)`) has none yet. `expected_type`
                                            // here is already `W A -> W B` (the type THIS call's
                                            // result must have, unified by the OUTER recursive
                                            // call against the already-checked later argument's
                                            // own inferred type) -- the signature's remaining,
                                            // still-unapplied params and its return, solved
                                            // against it, recover exactly that binding, PROVIDED
                                            // the later argument's own type came out concrete. A
                                            // bare, unannotated constructor application infers
                                            // its own type parameter as a hole by design
                                            // (`con_ref_result_type` declines it) -- that gap is
                                            // orthogonal to this one and stays open; this only
                                            // widens what `class_method_next_param` reads, it
                                            // doesn't change how any OTHER argument infers its
                                            // own type. `solve_typevars` never overwrites an
                                            // entry `dcc.subst` already set, so this is a
                                            // strictly additional source, not a relaxation of it.
                                            let remaining : Term :=
                                                rebuild_pi_chain (drop_params (I64.add (List.length args) 1) params) ret in
                                            let solved : List (Pair Identifier Term) :=
                                                solve_typevars scope remaining expected_type dcc.subst in
                                            let dom : Term := subst_typevars_term next_param solved in
                                            Option.some (CalleeDomain.mk dom decl.vars),
                                    },
                            },
                    },
            },
    }

/// A class method's declared signature, plus the names its class declaration
/// binds (`class_method_var_names`, `lang/src/scope.mo`) -- the wildcard set
/// `lam_binder_hint` rejects a discovered domain against.
struct ClassMethodDecl {
    sig : Term,
    vars : List Identifier,
}

/// The class method a reference names, or `Option.none` if `head` is not one.
/// Mirrors `type_check_free_var`'s own class-method test -- `ref_names_class_
/// method` for the qualifier rule (a qualifier naming an INDUCTIVE is a
/// constructor reference, not a class method) -- and takes its answer from the
/// same calls that test makes, so the domain the hint goes down with and the
/// resolution the reference gets cannot name different classes.
///
/// A QUALIFIED reference is decided by `class_method_ref` alone: the class the
/// qualifier names, and only that class. The bare-name scan cannot answer for
/// it, because class methods are registered under their bare name
/// (`add_methods_go`, `lang/scope.mo`) and the scan's answer is positional: both
/// `scope_data_add_class_def` and `scope_data_add_class` PREPEND (`lang/scope.
/// mo`), so the scan returns the LAST class declaring that name -- and a later-
/// declared class declaring the same method name would hand this argument
/// position a domain from a class the caller never named. That is the
/// `Bag.put x (fn q => ...)` case, and it is measured rather than assumed: with
/// `Bag` declared first and `Box` second, both declaring `put` over different
/// domains, the pre-fix checker gave `Bag.put`'s lambda binder `Box`'s domain
/// (`test_qualified_class_method_domain_comes_from_its_own_class`).
def class_method_declared_sig (head : Term) (scope : Scope) : Option ClassMethodDecl :=
    match term_peel head {
        Term.var idx dbg =>
            if I64.beq idx sentinel then
                match dbg {
                    DebugName.named id =>
                        if ref_names_class_method id scope then
                            match class_method_ref (scope_data_classes (scope_globals scope)) id {
                                Option.some ref => class_method_decl_of ref,
                                // No qualifier, so there is no class to honour and
                                // the bare-name scan is the only rule there is. It
                                // stays loose deliberately -- see `ref_names_class_
                                // method`'s comment on the un-dotted arm.
                                Option.none => class_method_declared_sig_bare id scope,
                            }
                        else
                            Option.none,
                    DebugName.unnamed => Option.none,
                }
            else
                Option.none,
        _ => Option.none,
    }

/// The declaration a resolved class-method reference names, in the shape the
/// lambda-binder hint wants: the signature, plus the names the class
/// declaration binds (`class_method_var_names`), which is the wildcard set
/// `lam_binder_hint` rejects a discovered domain against.
///
/// Takes the reference rather than the class and method in loose form, so both
/// arms of the lookup above hand the next step the same thing -- the qualified
/// one its own resolution, the unqualified one the resolution it stands in for.
def class_method_decl_of (found : ClassMethodRef) : Option ClassMethodDecl :=
    match found {
        ClassMethodRef.mk cls method =>
            match class_method_declared_type cls method {
                Option.none => Option.none,
                Option.some sig => Option.some (ClassMethodDecl.mk sig (class_method_var_names cls sig)),
            },
    }

/// The unqualified half of the lookup above: the first class in scope that
/// declares a method of this bare name. A method name declared by two classes
/// can still answer with the wrong one here, which is the pre-existing
/// looseness `ref_names_class_method` documents rather than a rule this
/// function introduces.
def class_method_declared_sig_bare (id : Identifier) (scope : Scope) : Option ClassMethodDecl :=
    let bare_id : Identifier :=
        match id { Identifier.id s => Identifier.id (last_dotted_segment s) } in
    match scope_find_class_def_by_name bare_id scope {
        err _ => Option.none,
        ok cd =>
            match scope_find_class cd.class_name scope {
                Option.none => Option.none,
                // The scan found the class, so the method it named is one this
                // class declares: the reference below is the resolution the scan
                // stands in for, not a guess.
                Option.some cls => class_method_decl_of (ClassMethodRef.mk cls cd.name),
            },
    }

/// Extract the return type from the function's type after application.
///
/// `#[terminating]`: R2b split the body by binder flavour, and the two halves
/// call back into this one on the stripped codomain, which is a subterm the
/// checker cannot see through the peel. It is the same argument the old
/// single-bodied version was making inline, now spread over three defs.
#[terminating]
def extract_pi_ret (f_term : Term) (a_term : Term) (f_typ : Term) (a_typ : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match f_typ {
        // A NON-EXPLICIT binder on the callee's type is not the arrow this
        // call is applying. Strip it and retry -- the old `Term.forall` arm
        // below. Without the guard the rule below would read a quantified
        // type variable's KIND as the parameter the argument is checked
        // against.
        Term.pi b _ _ =>
            if binder_is_explicit b
            then extract_pi_ret_explicit f_term a_term f_typ a_typ expected_type scope local_types locals
            else extract_pi_ret_strip f_term a_term f_typ a_typ expected_type scope local_types locals,
        // Stage 2: a path APPLICATION. The callee's type is a `PathP`,
        // which is not a Pi -- it reaches this arm because
        // `type_check_var` returns a variable's own type without
        // unifying it against the synthesized Pi the application was
        // checked against, and `try_type_check_def_call` declines
        // non-Pi signatures. The argument must be a DIMENSION, and the
        // result type is the line applied to it: `A d`.
        Term.cubical _c =>
            extract_path_app f_term a_term f_typ a_typ expected_type scope locals,
        _ => extract_non_pi_ret f_term a_term expected_type scope,
    }

/// The strip arm of `extract_pi_ret`.
def extract_pi_ret_strip (f_term : Term) (a_term : Term) (f_typ : Term) (a_typ : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match f_typ {
        Term.pi _b _dom cod => extract_pi_ret f_term a_term cod a_typ expected_type scope local_types locals,
        _ => err (TypeError.custom "extract_pi_ret_strip: expected a binder"),
    }

/// The explicit-arrow arm of `extract_pi_ret`. Split out so the merged
/// `Term.pi` arm above can dispatch on the binder without re-indenting it.
def extract_pi_ret_explicit (f_term : Term) (a_term : Term) (f_typ : Term) (a_typ : Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match f_typ {
        Term.pi _b pi_arg pi_ret =>
            let app_term : Term := Term.app f_term a_term in
            // A CONSTRUCTOR's callee type is not a real signature pi: for
            // a MULTI-argument constructor the callee is itself a partial
            // application, whose type came back as the pi
            // `type_check_app_ordinary` synthesized one level up
            // (`Term.pi <arg type> <this call's expected type>`) -- so
            // `pi_ret` here is that expected type, a HOLE in infer mode,
            // and peeling it discards the result type the innermost
            // reference already knew. Recover it the same way the non-pi
            // arm below does. `Wide.mk 10 20 30` is the shape that made
            // this matter: the single-argument `Slim.mk 1` never builds a
            // nested pi and so was already correct, which is exactly how
            // this narrowed down. A real (non-hole) `pi_ret` is a genuine
            // signature return type and always wins.
            //
            // ...but a REAL signature's `pi_ret` is a POLYMORPHIC one: it
            // keeps its implicit type variables FREE (`A -> List A -> List
            // A`), so peeling the chain alone reports the untouched
            // `pi_ret` (`List A -> List A`) and the variable never gets
            // instantiated -- the type travels upward still abstract, and
            // meets the declared return in `type_check_cases` as "type
            // mismatch: expected (List A), found (List U8)"
            // (`Sha256.hash_bytes`'s `List.flatten [...]`). The argument's
            // own already-inferred type is what says what the variables
            // are, and it is right here: solve `pi_arg` against `a_typ` the
            // way `def_call_continue` solves a def's declared parameters
            // against its arguments, and substitute through the WHOLE
            // remaining chain (not just the final return -- `cons e1 e2`
            // solves at the first argument and needs the second
            // parameter's own `List A` rewritten too).
            if is_hole pi_ret
            then ok (mk_typed app_term (con_spine_result_typ f_term pi_ret scope))
            else
                let pi_subst : List (Pair Identifier Term) := solve_typevars scope pi_arg a_typ List.empty in
                ok (mk_typed app_term (subst_typevars_term pi_ret pi_subst)),
        // Unreachable in practice -- the dispatcher above hands this
        // function only `Term.pi` -- but this match is over the full
        // `Term`, so the fallback stays rather than enumerating 14 arms
        // that could never be taken.
        _ => extract_non_pi_ret f_term a_term expected_type scope,
    }

/// The cubical arm of `extract_pi_ret`: a path APPLICATION. The callee's
/// type is a `PathP`, which is not a Pi -- it reaches the dispatcher
/// because `type_check_var` returns a variable's own type without
/// unifying it against the synthesized Pi the application was checked
/// against, and `try_type_check_def_call` declines non-Pi signatures. The
/// argument must be a DIMENSION, and the result type is the line applied
/// to it: `A d`.
def extract_path_app (f_term : Term) (a_term : Term) (f_typ : Term) (a_typ : Term)
    (expected_type : Term) (scope : Scope) (locals : LocalScope) : Result TypeError TypedTerm :=
    match path_parts_of f_typ {
        Option.some parts =>
            match unify a_typ cub_interval scope locals {
                err _ => err (TypeError.custom
                    "a path is applied at a dimension of the interval, not at a value"),
                ok _ =>
                    let result_typ : Term := Term.app parts.line a_term in
                    // `p i0`/`p i1` for a stuck `p` never reduces
                    // (`whnf_go`'s app arm needs a `Term.lam` head), but
                    // the path's own type CARRIES the endpoint, so checking
                    // the application AS the boundary term makes
                    // `p i0 ≡ a` hold by construction. Recorded limit:
                    // sufficient through `transp`/Stage 3, where boundary
                    // terms are paths applied at substituted endpoints, and
                    // NOT for Stage 5's eta-expanded paths.
                    match endpoint_of (whnf scope locals a_term) {
                        Option.some ep =>
                            match cubical_prim_eq ep CubicalPrim.i0 {
                                true => ok (mk_typed parts.left result_typ),
                                false => ok (mk_typed parts.right result_typ),
                            },
                        Option.none => ok (mk_typed (Term.app f_term a_term) result_typ),
                    },
            },
        // A cubical callee type that is not a saturated PathP is in no
        // shape to peel a return from: same fallback as the `_` arm.
        Option.none => extract_non_pi_ret f_term a_term (Term.hole) scope,
    }

/// The not-a-Pi continuation of `extract_pi_ret`: no return type to
/// peel. Factored out because both the `_` arm and the cubical arm's
/// fallback are this exact body.
def extract_non_pi_ret (f_term : Term) (a_term : Term) (expected_type : Term)
    (scope : Scope) : Result TypeError TypedTerm :=
    let app_term : Term := Term.app f_term a_term in
    // `f_typ` is not a pi chain, so there is no return type to
    // peel -- which is exactly the shape a CONSTRUCTOR reference
    // has: `type_check_free_var_con` has no per-constructor
    // signature to build a pi from (a constructor's params live
    // on its `InductConstructor`, and `ScopeDef.sig` is
    // unconditionally hole by design), so it returns the owning
    // inductive's named type directly (`con_ref_result_type`).
    // For a saturated `Slim.mk 1` that named type IS the
    // application's type, so echoing back a hole `expected_type`
    // discarded the one thing that was known -- leaving every
    // `let`-bound constructor value untyped and sending
    // `find_inductive_for_cases` into its ambiguous bare-name
    // scan (see `con_ref_result_type` for the stack-death that
    // followed). Prefer a real ambient expectation whenever
    // there is one; a genuinely unknown callee makes this a
    // no-op, since `f_typ` is then hole too.
    if is_hole expected_type
    then ok (mk_typed app_term (con_spine_result_typ f_term expected_type scope))
    else ok (mk_typed app_term expected_type)

/// The result type of an application spine whose head is a constructor
/// reference: the head's own already-inferred type, threaded back out
/// through however many argument layers the spine has.
///
/// `type_check_free_var`/`type_check_free_var_con` type a qualified
/// constructor reference as its owning inductive
/// (`qualified_con_ref_typ`), but each applied argument re-enters
/// `type_check_app_ordinary`, which checks the callee against a
/// SYNTHESIZED pi and then peels its return -- a hole while the call
/// itself is being inferred. Walking back to the spine head recovers the
/// type that was known all along. Returns `fallback` for any spine whose
/// head is not a typed constructor reference, so nothing else changes.
///
/// A location wrapper is transparent (R10). Both ends of the spine matter:
/// the head is where the wrapper would hide the constructor reference, and
/// an inner `app` is where one would end the walk early -- either way the
/// spine falls back, which is a silent downgrade to the inferred hole type
/// rather than an error.
#[partial]
def con_spine_result_typ (f_term : Term) (fallback : Term) (scope : Scope) : Term :=
    match f_term {
        Term.ctx _loc inner => con_spine_result_typ inner fallback scope,
        Term.app g _ => con_spine_result_typ g fallback scope,
        Term.var _ dbg => qualified_con_ref_typ dbg fallback scope,
        _ => fallback,
    }

/// Type check a binder over a type -- the ONE rule for all three flavours
/// (`BinderInfo.explicit`, `.binder`, `.level`). `type_check_forall` and
/// `type_check_pi` were two functions with this same body until R2b; the
/// only difference was that the Pi one ran its domain through
/// `pi_domain_level`, and that difference is provably vacuous here --
/// `pi_domain_level` answers `level_of_type arg_typ` on every branch except
/// a bare `Term.cubical` interval, and the old `forall` domain was always a
/// `Term.sort`, which is never one. So the merged rule applies
/// `pi_domain_level` unconditionally.
///
/// The universe is the `max` of the two components' sorts -- the standard rule,
/// and previously a flat level-1 sort that discarded both. `level_of_type`
/// answers `concrete 1` for a component that is not a known sort, so anything
/// outside the sort hierarchy contributes exactly what it contributed before;
/// what changes is a component that IS a sort, which now contributes its own
/// level instead of being ignored. The `max` is kept as structure rather than
/// folded to a numeral, which would need a case split for a level holding an
/// unresolved variable; every consumer that wants a numeral folds through
/// `level_const` anyway, so nothing is lost by leaving it as `max`.
///
/// The binder `b` is kept VERBATIM rather than rebuilt as `binder_anon`, as
/// the old Pi rule did. Rebuilding would erase both the name (which the
/// `forall` rule preserved, so a signature's variable names would silently
/// go) and the info (which would turn every generalization this rule types
/// into an ordinary arrow the next time anything looked at it).
def type_check_pi (b : Binder) (dom : Term) (cod : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match type_check dom Term.hole scope local_types locals {
        ok dom_tt =>
            let extended_types : List Term := List.cons dom local_types in
            match type_check cod Term.hole scope extended_types locals {
                ok cod_tt =>
                    let pi_term : Term := Term.pi b dom cod in
                    let universe : Term :=
                        Term.sort (SortLevel.max (pi_domain_level dom_tt.term dom_tt.typ)
                            (level_of_type cod_tt.typ)) in
                    ok (mk_typed pi_term universe),
                err e => err e,
            },
        err e => err e,
    }

/// The universe contribution of a Pi domain (Stage 1 step 4). A domain
/// that peels to the bare interval contributes `concrete 0`, because the
/// interval is a primitive KIND, not a resident of the universe
/// hierarchy: its checker-reported type is `Sort 1` (so `I : Type` holds,
/// matching the declared signature in the prelude's `with Cubical` block), and
/// `level_of_type` defaults a non-sort to `concrete 1` -- so without
/// this arm every `I -> A` lands one universe too high, bumping a
/// `Prop`-valued path family out of `Prop` and making Stage 2's
/// `PathP : (A : I -> Sort l) -> A i0 -> A i1 -> Sort l` unstateable at
/// `l = 0`. A dimension binder contributes nothing to the universe
/// level, which is the formation rule CCHM gives `PathP`.
///
/// The probe is on the CHECKED domain (`arg_tt.term`), not the raw one,
/// peeled through `Term.ctx` -- a Pi domain is type position, one of the
/// placement rules `kind_wants_loc` applies in `--debug` builds, so the
/// wrapper can sit right here and a direct match would see a non-debug
/// build accept what a debug build rejects: the exact split the
/// debug-transparency oracle exists to police. Checking first is also
/// what makes the SOURCE spelling work: a source `(i : I) -> A` lowers
/// the domain to a bare name reference, which only becomes the cubical
/// term inside `type_check` (the Stage 1 step 3 rewrite); the raw term a
/// `type_check_pi` caller hands in can be a `var` for exactly the same
/// domain. Anything that is not the bare interval keeps the ordinary
/// `level_of_type` answer, dimension expressions included: a non-bare
/// cubical term is still interval-valued, but it is not the kind itself.
def pi_domain_level (checked_arg : Term) (arg_typ : Term) : SortLevel :=
    match term_peel checked_arg {
        Term.cubical c =>
            match c {
                { prim := p, args := as } =>
                    if cubical_prim_eq p CubicalPrim.interval && List.is_empty as
                    then SortLevel.concrete 0
                    else level_of_type arg_typ,
            },
        _ => level_of_type arg_typ,
    }

/// Type check a sort universe level.
///
/// `Sort n : Sort m` holds exactly when `n < m`, which `level_lt` spells as
/// `succ level <= expected_level` — so those are one relation, and neither
/// is a special case.
///
/// The expected side is read through `sort_level_of`, so it is seen past a
/// location wrapper. That part is a real fix, not a tidy-up: the old arm
/// matched the expected term directly, so a `--debug` build's
/// `Term.ctx`-wrapped expected sort fell through to the error arm while the
/// non-debug build accepted it — exactly the kind of decision the
/// debug-transparency oracle forbids.
///
/// There used to be an `I64.beq expected_level level` arm before the
/// comparison, accepting `Sort n` against `Sort n` — a Type-in-Type hole.
/// The Rust core never had it: `infer(Sort{level})` gives `Sort (level+1)`,
/// which then fails `level+1 <= level`. Removed so the two agree.
def type_check_sort_full (sort_term : Term) (level : SortLevel) (expected_type : Term) : Result TypeError TypedTerm :=
    // A sort's own type is the sort one level up, always as `succ` -- which
    // folds (`level_const`) to the plain numeral a concrete level produced,
    // so no case split is needed here.
    let inferred : Term := Term.sort (SortLevel.succ level) in
    match sort_level_of expected_type {
        Option.some expected_level =>
            if level_lt level expected_level then
                ok (mk_typed sort_term expected_type)
            else
                err (TypeError.not_a_type sort_term),
        Option.none => match expected_type {
            Term.hole => ok (mk_typed sort_term inferred),
            _ => err (TypeError.not_a_type sort_term),
        },
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
/// kind of check. Neither `Term.con` nor `Term.ntv` is produced by this
/// codebase's own parser (`lang/parser.mo`); both exist for the
/// lowering/pretty-printing pipeline (`lang/lower_core_ir.mo`,
/// `lang/pretty.mo`) and hand-built test fixtures.
///
/// **But this def is on the compile path, and the comment that used to
/// say otherwise is how a miscompile hid here for weeks.**
/// `desugar_struct_lits_decls` (`lang/codegen/emit.mo`) rewrites every
/// annotated struct literal to a `Term.con` and hands the per-arg check
/// to the elaborate pass right after it — so every `monad build` of a
/// program holding one reaches this def. The constructor lookup below
/// used the wrong key until 2026-10-05, which failed elaboration for
/// all of them; see the regression rows beside `point_scope`.
/// Type check a cubical primitive application (Stage 1: the interval).
///
/// Every Stage 1 primitive is non-dependent, so the whole rule is an arity
/// check plus "each argument is an `I`":
///
///   I : Type        i0 : I        i1 : I
///   ineg  : I -> I        imeet, ijoin : I -> I -> I
///
/// `I : Type` rather than a universe of its own is the deliberate Stage 1
/// compromise recorded in `plans/type-system/univalence.md`: it makes `I` a
/// legitimate small type, which a full treatment would not, and the cost is
/// contained by `type_check_pi` treating an `I` DOMAIN as contributing level
/// 0 so a `Prop`-valued path family is not bumped out of `Prop`.
///
/// The arity check is here rather than in `Cubical` itself for the same
/// reason `Con` carries `num_args` and `type_check_con` validates it: the
/// representation stays simple and one place enforces the table.
/// `#[terminating]` for the same reason `type_check_lam` carries it: the
/// per-primitive dispatch tail-calls `type_check_pathp` and
/// `check_cubical_args_then`, members of the `type_check` cycle, with
/// nothing lexically smaller to pass. The recursion those calls feed
/// descends into the arguments of the cubical node being checked.
#[terminating]
def type_check_cubical (c : Cubical) (expected_type : Term) (scope : Scope)
    (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    let want : I64 := cubical_arity c.prim in
    if Bool.not (I64.beq (List.length c.args) want) then
        err (TypeError.custom (cubical_arity_message c.prim want (List.length c.args)))
    else
        // Every primitive gets an explicit arm: a `_ =>` here would
        // DEFEAT the coverage check (`validate_match_coverage`) and let a
        // future primitive fall silently into a rule that answers a
        // dimension question about it.
        match c.prim {
            CubicalPrim.pathp => type_check_pathp c.args expected_type scope local_types locals,
            CubicalPrim.transp => type_check_transp c.args expected_type scope local_types locals,
            CubicalPrim.interval =>
                check_cubical_args_then c expected_type scope local_types locals,
            CubicalPrim.i0 =>
                check_cubical_args_then c expected_type scope local_types locals,
            CubicalPrim.i1 =>
                check_cubical_args_then c expected_type scope local_types locals,
            CubicalPrim.ineg =>
                check_cubical_args_then c expected_type scope local_types locals,
            CubicalPrim.imeet =>
                check_cubical_args_then c expected_type scope local_types locals,
            CubicalPrim.ijoin =>
                check_cubical_args_then c expected_type scope local_types locals,
            // Stage 4's three are Stage-1-shaped: every argument is a
            // dimension, and the result is the prim's own row of
            // `cubical_result_type` -- `I` for the two face generators,
            // `Sort 1` for `is_one` (a former of types, the `l = 1`
            // discipline `PathP` uses). The generic tail handles all
            // three; `hcomp` (Stage 5) is the fourth bespoke rule,
            // because it is the first consumer of a cofibration and its
            // result is an argument rather than a row.
            CubicalPrim.face_eq0 =>
                check_cubical_args_then c expected_type scope local_types locals,
            CubicalPrim.face_eq1 =>
                check_cubical_args_then c expected_type scope local_types locals,
            CubicalPrim.is_one =>
                check_cubical_args_then c expected_type scope local_types locals,
            CubicalPrim.hcomp =>
                type_check_hcomp c.args expected_type scope local_types locals,
            // Stage 6b's witness is the second primitive typed entirely by
            // its `cubical_result_type` row: it takes no arguments and its
            // type does not depend on any (`is_one i1`), so the generic tail
            // is its whole rule.
            CubicalPrim.it_is_one =>
                check_cubical_args_then c expected_type scope local_types locals,
            // Stage 6b-ii: `Glue` is the second bespoke formation (after
            // `hcomp`), and its two projections are the first rules that
            // read a type back out of a cubical node.
            CubicalPrim.glue =>
                type_check_glue c.args expected_type scope local_types locals,
            CubicalPrim.glue_intro =>
                type_check_glue_intro c.args expected_type scope local_types locals,
            CubicalPrim.glue_elim =>
                type_check_glue_elim c.args expected_type scope local_types locals,
        }

/// The generic tail of `type_check_cubical` shared by every Stage 1
/// primitive: every argument is a dimension and the result is read off
/// the prim's own row of `cubical_result_type`. `PathP` is the exception
/// that forced the factoring -- its arguments are a line and two
/// endpoint VALUES, and its result type depends on the line -- so it
/// dispatches to `type_check_pathp` instead.
def check_cubical_args_then (c : Cubical) (expected_type : Term) (scope : Scope)
    (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match check_cubical_args c.args scope local_types locals {
        err e => err e,
        ok checked =>
            let inferred : Term := cubical_result_type c.prim in
            let rebuilt : Term := cub c.prim checked in
            match unify inferred expected_type scope locals {
                ok unified => ok (mk_typed rebuilt unified),
                err e => err e,
            },
    }

/// The formation rule for `transp A a : A i1` where
/// `A : I -> Sort l` and `a : A i0` (Stage 3,
/// plans/type-system/univalence.md). The line discipline is
/// `type_check_pathp`'s -- the same INFERRED line (the result type
/// `A i1` needs the line itself, and an echo of an expected `pi I _`
/// would lose it), the same `path_line_dom_ok` domain test, the same
/// `sort_level_of` codomain guard. The level is validated but not
/// consumed: `PathP` returns a SORT, so it needs `l`; `transp` returns
/// `A i1`, a term-level type, so the guard here only enforces that the
/// family really is a line INTO types. The element is checked against
/// `A i0` and unified against it -- the endpoint half of
/// `type_check_pathp_endpoints` for one endpoint, with the same
/// bidirectional-plus-unify discipline.
def type_check_transp (args : List Term) (expected_type : Term) (scope : Scope)
    (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    // Nested constructor patterns do not parse; the two args are
    // peeled one level at a time.
    match args {
        List.cons a_line rest =>
            match rest {
                List.cons a_elem rest2 =>
                    match rest2 {
                        List.empty =>
                            type_check_transp_go a_line a_elem expected_type scope local_types locals,
                        _ => err (TypeError.custom "transp takes 2 argument(s)"),
                    },
                _ => err (TypeError.custom "transp takes 2 argument(s)"),
            },
        // The arity table rejects every other argument count before this
        // runs; the arm exists only because the list has to be peeled.
        _ => err (TypeError.custom "transp takes 2 argument(s)"),
    }

/// The body of the formation rule once the two arguments have been
/// peeled apart (`type_check_transp` delegates here for the same
/// reason `type_check_pathp` does).
def type_check_transp_go (a_line : Term) (a_elem : Term) (expected_type : Term)
    (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match type_check a_line Term.hole scope local_types locals {
        err e => err e,
        ok line_tt =>
            match term_peel line_tt.typ {
                Term.pi _ dom cod =>
                    match path_line_dom_ok dom scope local_types locals {
                        false => err (TypeError.custom
                            "transp's first argument must be a line over the interval"),
                        true =>
                            match sort_level_of cod {
                                Option.none => err (TypeError.custom
                                    "transp's first argument must be a line into a sort"),
                                Option.some _l =>
                                    // WHNF first, and it is load-bearing: the
                                    // element of a `PathP`-valued family is a
                                    // path LAMBDA, and `check_path_lam` peels
                                    // the expected type BEFORE any reduction
                                    // -- an `App`-spelled `A i0` would fail
                                    // that peel and fall into the inferring
                                    // arm, rejecting a correct element.
                                    let elem_typ : Term :=
                                        whnf scope locals (Term.app line_tt.term cub_i0) in
                                    match type_check a_elem elem_typ scope local_types locals {
                                        err e => err e,
                                        ok elem_tt =>
                                            match unify elem_tt.typ elem_typ scope locals {
                                                err e => err e,
                                                ok _ =>
                                                    let rebuilt : Term :=
                                                        cub_transp line_tt.term elem_tt.term in
                                                    let result : Term :=
                                                        Term.app line_tt.term cub_i1 in
                                                    match unify result expected_type scope locals {
                                                        err e => err e,
                                                        ok unified =>
                                                            ok (mk_typed rebuilt unified),
                                                    },
                                            },
                                    },
                            },
                    },
                _ => err (TypeError.custom
                    "transp's first argument must be a line over the interval"),
            },
    }

/// The formation rule for `hcomp A φ u u0 : A`, where `A` is a type, `φ` a
/// cofibration, `u : I -> is_one φ -> A` a system, and `u0 : A` the
/// system's base (Stage 5, plans/type-system/univalence.md).
///
/// Unlike `PathP` and `transp`, the result type is an ARGUMENT: `transp`
/// reads `A i1` off the line it infers, but `hcomp`'s result is `A`
/// itself, and taking it from the EXPECTED type instead would make
/// `hcomp` uninferrable and would let a wrong `A` among the arguments
/// pass silently. So `A` is checked as a type and the remaining three
/// arguments are checked against it: `φ` against `I`, `u` against the Pi
/// `I -> is_one φ -> A` rebuilt from the checked `φ` and `A`, and `u0`
/// against `A` -- checked and then UNIFIED, the same
/// bidirectional-plus-unify discipline `transp` uses for its element,
/// since the var and constructor arms return their own types without
/// ever comparing against the expectation.
///
/// The result is unified with the expected type, so `hcomp` appears only
/// where its type is already known. That is the honest situation for a
/// Kan operation whose `A` cannot be recovered from the system alone.
def type_check_hcomp (args : List Term) (expected_type : Term) (scope : Scope)
    (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    // Nested constructor patterns do not parse; the four args are peeled
    // one level at a time.
    match args {
        List.cons a_typ rest =>
            match rest {
                List.cons a_face rest2 =>
                    match rest2 {
                        List.cons a_sys rest3 =>
                            match rest3 {
                                List.cons a_base rest4 =>
                                    match rest4 {
                                        List.empty =>
                                            type_check_hcomp_go a_typ a_face a_sys a_base
                                                expected_type scope local_types locals,
                                        _ => err (TypeError.custom "hcomp takes 4 argument(s)"),
                                    },
                                _ => err (TypeError.custom "hcomp takes 4 argument(s)"),
                            },
                        _ => err (TypeError.custom "hcomp takes 4 argument(s)"),
                    },
                _ => err (TypeError.custom "hcomp takes 4 argument(s)"),
            },
        // The arity table rejects every other argument count before this
        // runs; the arm exists only because the list has to be peeled.
        _ => err (TypeError.custom "hcomp takes 4 argument(s)"),
    }

/// The body of the formation rule once the four arguments are peeled
/// apart (`type_check_hcomp` delegates for the same reason
/// `type_check_transp` does).
def type_check_hcomp_go (a_typ : Term) (a_face : Term) (a_sys : Term) (a_base : Term)
    (expected_type : Term) (scope : Scope) (local_types : List Term)
    (locals : LocalScope) : Result TypeError TypedTerm :=
    // `A` is INFERRED, not checked: it is a type, and checking it against
    // a `Type` expectation would echo that expectation back as its own
    // type and lose the level the later unify needs. The sort guard is
    // what makes it a TYPE rather than an element -- `hcomp` composes in
    // a type, so `Sort l` for some `l` is the whole requirement.
    match type_check a_typ Term.hole scope local_types locals {
        err e => err e,
        ok typ_tt =>
            match sort_level_of typ_tt.typ {
                Option.none => err (TypeError.custom
                    "hcomp's first argument must be a type"),
                Option.some _l =>
                    match type_check a_face cub_interval scope local_types locals {
                        err e => err e,
                        ok face_tt =>
                            // `u : I -> is_one φ -> A`, built from the
                            // CHECKED `φ` and the checked `A` so the
                            // system is checked against the very types
                            // the other two arguments established.
                            let sys_typ : Term :=
                                Term.pi binder_anon cub_interval
                                    (Term.pi binder_anon (cub_is_one face_tt.term) typ_tt.term) in
                            match type_check a_sys sys_typ scope local_types locals {
                                err e => err e,
                                ok sys_tt =>
                                    match type_check a_base typ_tt.term scope local_types locals {
                                        err e => err e,
                                        ok base_tt =>
                                            match unify base_tt.typ typ_tt.term scope locals {
                                                err e => err e,
                                                ok _ =>
                                                    let rebuilt : Term :=
                                                        cub_hcomp typ_tt.term face_tt.term
                                                            sys_tt.term base_tt.term in
                                                    match unify typ_tt.term expected_type scope locals {
                                                        err e => err e,
                                                        ok unified =>
                                                            ok (mk_typed rebuilt unified),
                                                    },
                                            },
                                    },
                            },
                    },
            },
    }

// ─── Stage 6b-ii: Glue ──────────────────────────────────────────────────
//
// `Glue A φ T w` is CCHM's type former, and it is what makes univalence a
// theorem rather than an axiom. All three rules are bespoke for one shared
// reason: `w`'s type names `Equiv`, which lives in `proofs` -- ABOVE this
// checker -- so nothing here can refer to it by name. The helpers below
// build its `Sigma`/`Pi`/`PathP` unfolding instead. `univalence.md`'s
// 6b-ii measurement records why the alternative (moving `Equiv` down into
// the prelude so the rule could name it) is blocked by the Rust host's
// whole-corpus gate. The pin the plan prescribed for that trade-off -- one
// tying this unfolding to `Equiv`'s own -- is NOT expressible today
// (measured; both reasons are in the plan's 6b-ii section), so the shipped
// pin `test_glue_w_type_has_the_shape_of_equiv` covers only the kernel
// side and library drift is OPEN.

/// `Sigma`, as a term. It stays a NAME in the expansion -- an inductive
/// cannot be spelled any other way -- which is sound precisely because it
/// is already ambient from the prelude in every scope, `lang`'s included.
def equiv_sigma_ref : Term :=
    Term.var sentinel (DebugName.named (Identifier.id "Sigma"))

/// `A -> B` for two types at the caller's depth. Only `B` is shifted: a
/// `pi`'s `ret` sits one binder deeper and its `arg` does not.
def equiv_arrow (a : Term) (b : Term) : Term :=
    Term.pi binder_anon a (term_shift 1 b)

/// `Path A x y`, spelled as the primitive line `PathP (fn _ => A) x y` --
/// exactly the body `proofs/src/equiv.mo` gives `Path`.
def equiv_path (a_ty : Term) (a_left : Term) (a_right : Term) : Term :=
    cub_pathp (Term.lam binder_anon cub_interval (term_shift 1 a_ty)) a_left a_right

/// `Sigma A (fn _ => body)`, with `body` at depth one deeper.
def equiv_sigma (a_ty : Term) (a_body : Term) : Term :=
    Term.app (Term.app equiv_sigma_ref a_ty) (Term.lam binder_anon a_ty a_body)

/// `isContr A := Sigma A (fn center => (x : A) -> Path A x center)`.
def equiv_is_contr (a_ty : Term) : Term :=
    equiv_sigma a_ty
        (Term.pi binder_anon (term_shift 1 a_ty)
            (equiv_path (term_shift 2 a_ty) (Term.var 0 DebugName.unnamed)
                (Term.var 1 DebugName.unnamed)))

/// `fiber A B f b := Sigma A (fn a => Path B (f a) b)`, for the four terms
/// at the caller's depth.
def equiv_fiber (a_ty : Term) (b_ty : Term) (a_fun : Term) (a_point : Term) : Term :=
    equiv_sigma a_ty
        (equiv_path (term_shift 1 b_ty)
            (Term.app (term_shift 1 a_fun) (Term.var 0 DebugName.unnamed))
            (term_shift 1 a_point))

/// `Equiv X Y := Sigma (X -> Y) (fn f => (b : Y) -> isContr (fiber X Y f b))`
/// -- the library def's unfolding, one helper per level of it.
///
/// `pub` for the shape pin (`test_glue_w_type_has_the_shape_of_equiv`,
/// `proofs/src/checker/cubical_props.mo`), which reads the assembled type
/// rather than any intermediate -- the same reason `as_cubical_type`
/// (`whnf.mo`) is `pub`.
pub def equiv_type (a_x : Term) (a_y : Term) : Term :=
    equiv_sigma (equiv_arrow a_x a_y)
        (Term.pi binder_anon (term_shift 1 a_y)
            (equiv_is_contr
                (equiv_fiber (term_shift 2 a_x) (term_shift 2 a_y)
                    (Term.var 1 DebugName.unnamed)
                    (Term.var 0 DebugName.unnamed))))

/// `w : (u : is_one φ) -> Equiv (T u) A` -- `Glue`'s fourth argument's type.
def glue_equiv_type (a_typ : Term) (a_face : Term) (a_partial : Term) : Term :=
    Term.pi binder_anon (cub_is_one a_face)
        (equiv_type (Term.app (term_shift 1 a_partial) (Term.var 0 DebugName.unnamed))
            (term_shift 1 a_typ))

/// `T : is_one φ -> T u`'s type, i.e. the system type `glue`'s `t` is
/// checked against (and the type of an `hcomp` system).
def glue_system_type (a_face : Term) (a_partial : Term) : Term :=
    Term.pi binder_anon (cub_is_one a_face)
        (Term.app (term_shift 1 a_partial) (Term.var 0 DebugName.unnamed))

/// The checked first four arguments of a `Glue` node, plus the sort level
/// its partial type lands in. Shared by the formation and the introduction
/// so the two cannot check different things.
struct GlueParams {
    typ_ : Term,
    face_ : Term,
    partial_ : Term,
    equiv_ : Term,
    level_ : SortLevel,
}

/// Check `A`, `φ`, `T` and `w` against `Glue`'s four parameter types.
def check_glue_params (a_typ : Term) (a_face : Term) (a_partial : Term) (a_equiv : Term)
    (scope : Scope) (local_types : List Term) (locals : LocalScope)
    : Result TypeError GlueParams :=
    // `A` is INFERRED with a sort guard, exactly as `hcomp`'s is: checking
    // it against `Type` would echo that expectation back and lose the level.
    match type_check a_typ Term.hole scope local_types locals {
        err e => err e,
        ok typ_tt =>
            match sort_level_of typ_tt.typ {
                Option.none => err (TypeError.custom "Glue's first argument must be a type"),
                Option.some _l =>
                    match type_check a_face cub_interval scope local_types locals {
                        err e => err e,
                        ok face_tt =>
                            // `T` is INFERRED and peeled to a `pi`, like
                            // `PathP`'s line: its codomain's level IS the
                            // level `Glue` lands in, and a checked `pi
                            // (is_one φ) (Sort _)` expectation would lose it.
                            match type_check a_partial Term.hole scope local_types locals {
                                err e => err e,
                                ok partial_tt =>
                                    match term_peel partial_tt.typ {
                                        Term.pi _ dom cod =>
                                            match unify dom (cub_is_one face_tt.term)
                                                scope locals {
                                                err _ => err (TypeError.custom
                                                    "Glue's third argument must be a partial type over `is_one φ`"),
                                                ok _ =>
                                                    match sort_level_of cod {
                                                        Option.none => err (TypeError.custom
                                                            "Glue's third argument must be a line into a sort"),
                                                        Option.some l =>
                                                            match type_check a_equiv
                                                                (glue_equiv_type typ_tt.term
                                                                    face_tt.term partial_tt.term)
                                                                scope local_types locals {
                                                                err e => err e,
                                                                ok equiv_tt =>
                                                                    ok (GlueParams.mk
                                                                        typ_tt.term face_tt.term
                                                                        partial_tt.term
                                                                        equiv_tt.term l),
                                                            },
                                                    },
                                            },
                                        _ => err (TypeError.custom
                                            "Glue's third argument must be a partial type over `is_one φ`"),
                                    },
                            },
                    },
            },
    }

/// `Glue A φ T w : Sort l` -- the formation rule (Stage 6b-ii). The result
/// is the sort `T`'s codomain lands in, the same level discipline
/// `type_check_pathp` uses for a line.
def type_check_glue (args : List Term) (expected_type : Term) (scope : Scope)
    (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    // Nested constructor patterns do not parse; the four args are peeled
    // one level at a time.
    match args {
        List.cons a_typ rest =>
            match rest {
                List.cons a_face rest2 =>
                    match rest2 {
                        List.cons a_partial rest3 =>
                            match rest3 {
                                List.cons a_equiv rest4 =>
                                    match rest4 {
                                        List.empty =>
                                            match check_glue_params a_typ a_face a_partial
                                                a_equiv scope local_types locals {
                                                err e => err e,
                                                ok p =>
                                                    match p {
                                                        GlueParams.mk a b c d l =>
                                                            match unify (Term.sort l)
                                                                expected_type scope locals {
                                                                err e => err e,
                                                                ok unified => ok (mk_typed
                                                                    (cub_glue a b c d) unified),
                                                            },
                                                    },
                                            },
                                        _ => err (TypeError.custom "Glue takes 4 argument(s)"),
                                    },
                                _ => err (TypeError.custom "Glue takes 4 argument(s)"),
                            },
                        _ => err (TypeError.custom "Glue takes 4 argument(s)"),
                    },
                _ => err (TypeError.custom "Glue takes 4 argument(s)"),
            },
        // The arity table rejects every other argument count before this
        // runs; the arm exists only because the list has to be peeled.
        _ => err (TypeError.custom "Glue takes 4 argument(s)"),
    }

/// `glue A φ T w t a : Glue A φ T w` -- the introduction (Stage 6b-ii).
///
/// Unlike CCHM's `glue t a`, the formation's four arguments are carried
/// explicitly, because the reduction `glue ... t a ≡ t it_is_one` fires at
/// the literal `i1` and `whnf` has no expected type to read φ from. The
/// consequence is that the result type needs nothing from the expectation
/// to be COMPUTED -- it is rebuilt from the checked arguments -- and the
/// expectation is only unified against at the end.
///
/// `t : (u : is_one φ) -> T u` and `a : A`. The compatibility condition
/// `w (t u) = a` on φ is NOT checked, the same unenforced shape as
/// `hcomp`'s `u i0 = u0` (finding 6 records it as deliberate).
def type_check_glue_intro (args : List Term) (expected_type : Term) (scope : Scope)
    (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match args {
        List.cons a_typ rest =>
            match rest {
                List.cons a_face rest2 =>
                    match rest2 {
                        List.cons a_partial rest3 =>
                            match rest3 {
                                List.cons a_equiv rest4 =>
                                    match rest4 {
                                        List.cons a_sys rest5 =>
                                            match rest5 {
                                                List.cons a_base rest6 =>
                                                    match rest6 {
                                                        List.empty =>
                                                            match check_glue_params a_typ a_face
                                                                a_partial a_equiv scope
                                                                local_types locals {
                                                                err e => err e,
                                                                ok p =>
                                                                    match p {
                                                                        GlueParams.mk ga gf gt gw _l =>
                                                                            match type_check a_sys
                                                                                (glue_system_type gf gt)
                                                                                scope local_types locals {
                                                                                err e => err e,
                                                                                ok sys_tt =>
                                                                                    match type_check a_base ga
                                                                                        scope local_types locals {
                                                                                        err e => err e,
                                                                                        ok base_tt =>
                                                                                            match unify base_tt.typ ga scope locals {
                                                                                                err e => err e,
                                                                                                ok _ =>
                                                                                                    // Expectation FIRST here, unlike
                                                                                                    // `check_cubical_args_then`'s
                                                                                                    // `unify inferred expected`: `unify`
                                                                                                    // has no `Term.cubical` arm, so an
                                                                                                    // INFERRING caller's bare `Term.hole`
                                                                                                    // would be a mismatch on the second
                                                                                                    // side. On the first it is the
                                                                                                    // wildcard it means, and a real
                                                                                                    // expectation still reports a
                                                                                                    // genuine mismatch.
                                                                                                    match unify expected_type (cub_glue ga gf gt gw) scope locals {
                                                                                                        err e => err e,
                                                                                                        ok unified => ok (mk_typed
                                                                                                            (cub_glue_intro ga gf gt gw sys_tt.term base_tt.term)
                                                                                                            unified),
                                                                                                    },
                                                                                            },
                                                                                    },
                                                                            },
                                                                    },
                                                            },
                                                        _ => err (TypeError.custom "glue takes 6 argument(s)"),
                                                    },
                                                _ => err (TypeError.custom "glue takes 6 argument(s)"),
                                            },
                                        _ => err (TypeError.custom "glue takes 6 argument(s)"),
                                    },
                                _ => err (TypeError.custom "glue takes 6 argument(s)"),
                            },
                        _ => err (TypeError.custom "glue takes 6 argument(s)"),
                    },
                _ => err (TypeError.custom "glue takes 6 argument(s)"),
            },
        _ => err (TypeError.custom "glue takes 6 argument(s)"),
    }

/// The `A` of a `Glue A φ T w` type, or none when `t` is not one.
///
/// The UNREDUCED spelling is read first and `whnf` is only the fallback,
/// which is load-bearing rather than an optimisation: `whnf` reduces
/// `Glue A i1 T w` to `T it_is_one` (`whnf_glue`), so reducing first would
/// make every `unglue` at the literal endpoint fail to find its `Glue` and
/// report "must be a Glue type" for a term that is one.
def glue_base_of (t : Term) (scope : Scope) (locals : LocalScope) : Option Term :=
    match glue_base_of_head t {
        Option.some a => Option.some a,
        Option.none => glue_base_of_head (whnf scope locals t),
    }

/// The head read on its own, so `glue_base_of` states the order once.
def glue_base_of_head (t : Term) : Option Term :=
    match term_peel t {
        Term.cubical c =>
            match c {
                { prim := q, args := as } =>
                    if cubical_prim_eq q CubicalPrim.glue then
                        match as {
                            List.cons a_typ _rest => Option.some a_typ,
                            // `cubical_arity` already fixed the count at
                            // four; the arm exists only because the list is
                            // peeled.
                            List.empty => Option.none,
                        }
                    else Option.none,
            },
        _ => Option.none,
    }

/// `unglue g : A` for `g : Glue A φ T w` -- the elimination (Stage 6b-ii).
///
/// The result is read OFF the argument's inferred type, via
/// `glue_base_of`. A `g` whose type is not a `Glue` is rejected rather
/// than left with a stuck type.
def type_check_glue_elim (args : List Term) (expected_type : Term) (scope : Scope)
    (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match args {
        List.cons a_glued rest =>
            match rest {
                List.empty =>
                    match type_check a_glued Term.hole scope local_types locals {
                        err e => err e,
                        ok glued_tt =>
                            match glue_base_of glued_tt.typ scope locals {
                                Option.some a_typ =>
                                    // Expectation first, for the reason
                                    // `type_check_glue_intro` states: an
                                    // inferring caller's expectation is a
                                    // bare `Term.hole`, and `A` is a cubical
                                    // term only `Similar` can match.
                                    match unify expected_type a_typ scope locals {
                                        err e => err e,
                                        ok unified => ok (mk_typed
                                            (cub_glue_elim glued_tt.term) unified),
                                    },
                                Option.none => err (TypeError.custom
                                    "unglue's argument must be a Glue type"),
                            },
                    },
                _ => err (TypeError.custom "unglue takes 1 argument(s)"),
            },
        _ => err (TypeError.custom "unglue takes 1 argument(s)"),
    }

/// The formation rule for `PathP A a b : Sort l` where
/// `A : I -> Sort l` (Stage 2, plans/type-system/univalence.md).
///
/// The line is INFERRED, not checked against a `pi I _` expected type:
/// checking would echo that expected type back as the line's own type,
/// and the codomain's level -- the `l` of the result -- would be lost
/// before it could be read. Inference is safe here because both line
/// spellings infer: a named line carries its declared signature, and a
/// lambda infers a Pi whose domain is a hole (unannotated binder) or the
/// checked interval (annotated one).
///
/// The endpoints are checked against `A i0`/`A i1` and then UNIFIED
/// against it explicitly: the var and constructor arms return their own
/// types without comparing against the expectation, so without the
/// `unify` a boundary endpoint of the wrong type would be accepted
/// vacuously. The result type is `Sort l` -- the sort the line lands
/// in, which `pi_domain_level` already made an `I` domain contribute
/// `concrete 0` to, so a `Prop`-valued path family stays in `Prop`.
def type_check_pathp (args : List Term) (expected_type : Term) (scope : Scope)
    (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    // Nested constructor patterns do not parse; the three args are
    // peeled one level at a time.
    match args {
        List.cons a_line rest =>
            match rest {
                List.cons a_left rest2 =>
                    match rest2 {
                        List.cons a_right rest3 =>
                            match rest3 {
                                List.empty =>
                                    type_check_pathp_go a_line a_left a_right expected_type
                                        scope local_types locals,
                                _ => err (TypeError.custom "PathP takes 3 argument(s)"),
                            },
                        _ => err (TypeError.custom "PathP takes 3 argument(s)"),
                    },
                _ => err (TypeError.custom "PathP takes 3 argument(s)"),
            },
        // The arity table rejects every other argument count before this
        // runs; the arm exists only because the list has to be peeled.
        _ => err (TypeError.custom "PathP takes 3 argument(s)"),
    }

/// The body of the formation rule once the three arguments have been
/// peeled apart (the nested `List.cons` pattern does not parse, so
/// `type_check_pathp` peels and delegates here).
def type_check_pathp_go (a_line : Term) (a_left : Term) (a_right : Term) (expected_type : Term)
    (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match type_check a_line Term.hole scope local_types locals {
        err e => err e,
        ok line_tt =>
            match term_peel line_tt.typ {
                Term.pi _ dom cod =>
                    match path_line_dom_ok dom scope local_types locals {
                        false => err (TypeError.custom
                            "PathP's first argument must be a line over the interval"),
                        true =>
                            match sort_level_of cod {
                                Option.some l =>
                                    match type_check_pathp_endpoints line_tt.term a_left a_right
                                        scope local_types locals {
                                        err e => err e,
                                        ok rebuilt =>
                                            match unify (Term.sort l) expected_type scope locals {
                                                err e => err e,
                                                ok unified => ok (mk_typed rebuilt unified),
                                            },
                                    },
                                Option.none => err (TypeError.custom
                                    "PathP's first argument must be a line into a sort"),
                            },
                    },
                _ => err (TypeError.custom
                    "PathP's first argument must be a line over the interval"),
            },
    }

/// The line-domain half of the `PathP` formation rule. A HOLE domain is
/// an unannotated line binder (`fn i => ...`): nothing is knowable about
/// it, and the rule's own `I` domain is forced below by the boundary
/// application, so it is accepted as-is. Anything else must check AS the
/// bare interval -- the CHECKED term is compared because a source
/// spelling lowers the domain to a bare name reference, which only
/// becomes the cubical term inside `type_check` (Stage 1 step 3's
/// rewrite), so the raw domain a Pi hands in can be a `var`.
def path_line_dom_ok (dom : Term) (scope : Scope) (local_types : List Term)
    (locals : LocalScope) : Bool :=
    if is_hole dom
    then true
    else match type_check dom Term.hole scope local_types locals {
        err _ => false,
        ok dom_tt => peels_to_bare_interval dom_tt.term,
    }

/// The endpoint half of the `PathP` formation rule: `a` against `A i0`,
/// `b` against `A i1`, each checked with the real expected type (so
/// bidirectional checking sees it) and then unified against it (so the
/// comparison cannot be skipped). Returns the rebuilt `PathP` over the
/// checked components.
def type_check_pathp_endpoints (line : Term) (a_left : Term) (a_right : Term) (scope : Scope)
    (local_types : List Term) (locals : LocalScope) : Result TypeError Term :=
    let left_typ : Term := Term.app line cub_i0 in
    match type_check a_left left_typ scope local_types locals {
        err e => err e,
        ok left_tt =>
            match unify left_tt.typ left_typ scope locals {
                err e => err e,
                ok _ =>
                    let right_typ : Term := Term.app line cub_i1 in
                    match type_check a_right right_typ scope local_types locals {
                        err e => err e,
                        ok right_tt =>
                            match unify right_tt.typ right_typ scope locals {
                                err e => err e,
                                ok _ =>
                                    ok (cub_pathp line left_tt.term right_tt.term),
                            },
                    },
            },
    }

/// What a primitive's application is a term OF. `interval` is the type
/// former, so it answers a sort; everything else in Stage 1 is interval-
/// valued. `is_one` is the other former here: it answers `Sort 1`, the
/// `l = 1` discipline `PathP` uses. `pathp`'s, `transp`'s and `hcomp`'s
/// rows are never consulted -- `type_check_cubical` routes all three to
/// their own rules (`type_check_pathp`, `type_check_transp`,
/// `type_check_hcomp`) because each result depends on an ARGUMENT (the
/// line, or the type being composed in), which no prim-keyed table can
/// state -- but the rows exist all the same: they are what makes a
/// missing arm a compile error rather than a silent future crash
/// (`validate_match_coverage`, `lang/src/typecheck/infer.mo`).
def cubical_result_type (prim : CubicalPrim) : Term := match prim {
    CubicalPrim.interval => sort_n 1,
    CubicalPrim.i0 => cub_interval,
    CubicalPrim.i1 => cub_interval,
    CubicalPrim.ineg => cub_interval,
    CubicalPrim.imeet => cub_interval,
    CubicalPrim.ijoin => cub_interval,
    CubicalPrim.pathp => Term.hole,
    CubicalPrim.transp => Term.hole,
    CubicalPrim.face_eq0 => cub_interval,
    CubicalPrim.face_eq1 => cub_interval,
    CubicalPrim.is_one => sort_n 1,
    CubicalPrim.hcomp => Term.hole,
    CubicalPrim.it_is_one => cub_is_one cub_i1,
    // Stage 6b-ii's three are all bespoke: `Glue`'s result is the sort
    // its partial type lands in, and the other two read their types off
    // the Glue they are applied to.
    CubicalPrim.glue => Term.hole,
    CubicalPrim.glue_intro => Term.hole,
    CubicalPrim.glue_elim => Term.hole,
}

/// Every Stage 1 argument is a dimension, i.e. an `I`. When `PathP` lands
/// its first argument is a line of types instead, which is why this is a
/// helper rather than inlined.
#[partial]
def check_cubical_args (args : List Term) (scope : Scope) (local_types : List Term)
    (locals : LocalScope) : Result TypeError (List Term) :=
    match args {
        List.empty => ok List.empty,
        List.cons hd rest =>
            match type_check hd cub_interval scope local_types locals {
                err e => err e,
                ok hd_tt =>
                    match check_cubical_args rest scope local_types locals {
                        err e => err e,
                        ok rest_checked => ok (List.cons hd_tt.term rest_checked),
                    },
            },
    }

def cubical_arity_message (prim : CubicalPrim) (want : I64) (got : I64) : String :=
    let head : String := String.concat "cubical primitive `" (cubical_prim_name prim) in
    let mid : String := String.concat head "` takes " in
    let w : String := String.concat mid (I64.to_string want) in
    let a : String := String.concat w " argument(s), got " in
    String.concat a (I64.to_string got)

def type_check_con (c : Con) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match c {
        mk cname typ_name num_args args =>
            match typ_name {
                NamePath.mk ids =>
                    let full_name : NamePath := NamePath.mk (list_append ids (List.cons cname List.empty)) in
                    // The lookup key is the BARE name: both
                    // `build_scope_struct` and the parser register a
                    // constructor under a one-segment path (`[mk]`), never
                    // `[Type, mk]`. `full_name` is for the diagnostics only.
                    let bare_con : NamePath := NamePath.mk (List.cons cname List.empty) in
                    match scope_find_inductive typ_name scope {
                        err _ =>
                            match check_con_args_untyped args scope local_types locals {
                                ok elab_args => ok (mk_typed (Term.con (Con.mk cname typ_name num_args elab_args)) expected_type),
                                err e => err e,
                            },
                        ok ind =>
                            match find_constructor_in_inductive ind bare_con {
                                Option.none => err (TypeError.unknown_constructor (NameRef.nnp full_name)),
                                Option.some ctor =>
                                    match ctor {
                                        InductConstructor.mk _ params _ =>
                                            if I64.beq num_args (List.length params) then
                                                let bindings : List (Pair Identifier Term) := con_own_param_bindings ind expected_type in
                                                match check_con_args_against_params args params bindings scope local_types locals {
                                                    ok elab_args => ok (mk_typed (Term.con (Con.mk cname typ_name num_args elab_args)) (con_result_type ind expected_type)),
                                                    err e => err e,
                                                }
                                            else
                                                err (TypeError.custom (con_arity_msg full_name num_args (List.length params)))
                                    }
                            }
                    }
            }
    }

/// A constructor application's own result type, for the INFER case.
///
/// `type_check_con` used to return `expected_type` verbatim, which in
/// infer mode (`Term.hole`) meant a constructor application had no
/// inferred type at all -- even though the owning `Inductive` was
/// resolved (`scope_find_inductive`) and its constructor found and
/// arity-checked immediately above. That hole then propagated: an
/// unannotated `let s := Slim.mk 1` desugars to `Term.app (Term.lam s
/// hole ...) (Slim.mk 1)` (`desugar_do_inner`'s `let_s`, lang/types.mo),
/// `type_check_app_ordinary` builds its Pi from the ARGUMENT's inferred
/// type, and `type_check_lam`'s own `if is_hole t then arg_typ else t`
/// preference (see its doc comment, which names this very scenario)
/// then had two holes to choose between -- so `s`'s local type stayed
/// hole, `find_inductive_for_cases` fell past `con_owner_name` (the
/// scrutinee is a VARIABLE now, not a `Term.con`) and `type_head_name`
/// down to the ambiguous constructor-name scan, and
/// `find_inductive_for_cases_by_constructor` correctly errored on a
/// bare name two inductives share (`mk`). Under codegen's best-effort
/// elaboration (`elaborate_module_decls_best_effort`, lang/module.mo,
/// which swallows a failing decl unchanged by design) that error left
/// the match arms' binders untyped, so `+` stayed a GENERIC class call
/// and its dictionary (`Add_A_add` -> `__Dict_Add_A` ->
/// `Add_A_add_closure_shim` -> `Add_A_add`) recursed until the stack
/// died -- confirmed live as a SIGSEGV in `Add_A_add`'s prologue
/// `movaps`, on a program whose IR was otherwise correct.
///
/// Returns the inductive's own named type in the `Term.var sentinel
/// (DebugName.named ...)` shape `type_head_name` consumes -- exactly
/// what `type_check_struct_lit` returns for an explicitly-annotated
/// literal, via the same `inductive_bare_name` helper. A real ambient
/// `expected_type` is always preferred and never overridden, so this
/// only ever ADDS precision where there was none, matching
/// `find_inductive_for_cases`'s own "only ever add a strictly-better
/// preferred path, never change the shared fallback" discipline.
def con_result_type (ind : Inductive) (expected_type : Term) : Term :=
    if is_hole expected_type && Bool.not (inductive_has_params ind)
    then Term.var sentinel (DebugName.named (inductive_bare_name ind))
    else expected_type

/// `ind`'s own type head (`inductive_bare_name ind`), applied to its own
/// declared PARAM NAMES in declaration order -- `ResultT E M A` for
/// `ResultT`'s three type params, as a symbolic "shape" to unify a real
/// applied type against (`bind_term_vars`'s own `shape` argument).
#[partial]
def inductive_applied_to_own_params (ind : Inductive) (names : List Identifier) : Term :=
    match ind {
        Inductive.mk _ _ _ _ _ _ =>
            apply_term_to_named_vars (Term.var sentinel (DebugName.named (inductive_bare_name ind))) names
    }

#[partial]
def apply_term_to_named_vars (head : Term) (names : List Identifier) : Term :=
    match names {
        List.empty => head,
        List.cons n rest => apply_term_to_named_vars (Term.app head (Term.var sentinel (DebugName.named n))) rest,
    }

/// Bindings for `ind`'s own type params (`E`, `M`, `A` for `ResultT`),
/// recovered by unifying `ind` applied to those names against the real
/// `expected_type` -- `instance [Monad M] Monad (ResultT E M)`'s own
/// `carrier_bindings` does the identical job for an INSTANCE's wildcard
/// args; this is the constructor-argument-checking sibling that case
/// never covered. `List.empty` when `expected_type` carries no real
/// information (a hole/placeholder): `bind_term_vars` would just fail to
/// match a concrete shape against a hole, so skip it rather than let it
/// try.
///
/// Without this, `check_con_args_against_params` checked each arg
/// against the constructor's LITERAL declared param type -- `run : M
/// (Result E A)` for `ResultT.mk`, with `M`/`E`/`A` still the type's own
/// abstract parameters, never substituted with what `expected_type`
/// (`ResultT String IO Content`) already says they are. A `do`-block
/// argument's `Monad.pure`/`Monad.bind` call then had no concrete carrier
/// to resolve against (`resolve_class_method`'s own `expected_type`
/// channel, `carrier_from_expected_type`), silently fell through to the
/// unresolved-sentinel fallback (this file's own `err _ =>` arm just
/// above `resolve_class_method`'s call site), and surfaced many stages
/// later as `no instance found for `Monad.pure`` once codegen's
/// reachability gate ran -- MEASURED on `motes/shuttle`'s `registry_tests.
/// mo`/`ollama_e2e_tests.mo` (`run_tool`, `mk_tool`), both `ResultT`-typed.
#[partial]
def con_own_param_bindings (ind : Inductive) (expected_type : Term) : List (Pair Identifier Term) :=
    if is_hole expected_type then List.empty
    else
        match ind {
            Inductive.mk _ params _ _ _ _ =>
                let names : List Identifier := param_names params in
                bind_term_vars names (inductive_applied_to_own_params ind names) expected_type List.empty
        }

/// Substitute every `(name, type)` binding `con_own_param_bindings`
/// recovered into one constructor param's declared type, one name at a
/// time -- `name_subst_term` is a free-variable substitution, so this is
/// sound even though `t` may mention more than one of `ind`'s own params.
#[partial]
def apply_con_param_bindings (bindings : List (Pair Identifier Term)) (t : Term) : Term :=
    match bindings {
        List.empty => t,
        List.cons b rest =>
            match b { Pair.pair name repl => apply_con_param_bindings rest (name_subst_term name repl t) },
    }

def con_arity_msg (full_name : NamePath) (got : I64) (want : I64) : String :=
    "constructor arity mismatch: " ++ show_name_path full_name ++ " expects "
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
/// `core/src/core_check.rs`'s `desugar_struct_literals`). The literal's
/// FIELD SET is validated first, by the same rule a named call uses
/// (`field_set_validate`): a written name no declared field matches is an
/// error, and a declared field the literal omits is an error unless it
/// carries a `:=` default. Both compilers enforce it (`check_struct_fields`
/// on the Rust side); before 2026-10-28 both accepted a typo'd name and an
/// omitted required field silently, and the hole the omission left is what
/// `lower_sparse_args` truncates an allocation at.
def type_check_struct_lit (fields : List StructLitField) (type_name : Option Term) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError TypedTerm :=
    match struct_lit_head_name type_name expected_type {
        Option.none =>
            err (TypeError.custom "cannot infer struct type for struct literal (no `: StructName` annotation and no expected type from context)"),
        Option.some sname =>
            let typ_mp : NamePath := NamePath.mk (List.cons sname List.empty) in
            match scope_find_inductive typ_mp scope {
                err _ => err (TypeError.unknown_type (NameRef.nnp typ_mp)),
                ok ind =>
                    match ind {
                        Inductive.mk _ _ _ ctors _ _ =>
                            match ctors {
                                List.empty => err (TypeError.custom (String.concat "struct has no registered constructor: " (show_name_path typ_mp))),
                                List.cons ctor _ =>
                                    match ctor {
                                        InductConstructor.mk con_name params _ =>
                                            // The field SET first: an unknown
                                            // name used to be dropped and an
                                            // uncovered field lowered to a
                                            // hole `lower_sparse_args` truncates
                                            // the allocation at -- a silent
                                            // wrong program, and a SIGSEGV in
                                            // the compiled binary.
                                            match field_set_validate "struct literal" params fields {
                                                err e => err e,
                                                ok _ =>
                                            let args : List (Option Term) := struct_lit_build_args params fields in
                                            let bindings : List (Pair Identifier Term) := con_own_param_bindings ind expected_type in
                                            match check_con_args_against_params args params bindings scope local_types locals {
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

/// `InductConstructor.mk`'s own `name` field is a full `NamePath`
/// (`build_scope_struct` registers it as `NamePath.mk [mk]`) --
/// `Con.mk` wants just the bare constructor `Identifier`, same as
/// every other constructor-application site in this file.
def struct_lit_con_name (np : NamePath) : Identifier :=
    match np {
        NamePath.mk ids =>
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
/// Whether an argument's already-SUCCESSFUL ordinary check should be
/// trusted, or is only vacuously successful and must not preempt a
/// named-call spread. Mirrors the reference compiler's own
/// `struct_literal_arg_matches_expected` (`core/src/core_check.rs`),
/// added there after the identical real failure.
///
/// `type_check_struct_lit` is deliberately LAX about a literal's field
/// set: given an expected type, it takes that type's FIRST constructor
/// and walks the CONSTRUCTOR's own declared params, silently producing
/// `Option.none` for every param the literal doesn't mention and
/// ignoring every literal field the constructor doesn't declare. So an
/// unannotated literal whose fields don't overlap the expected type at
/// ALL still "checks" fine against it -- nothing is ever compared --
/// and desugars to a constructor application with zero real arguments.
///
/// That is exactly the shape a genuine NAMED CALL produces
/// (`callee { param := v, ... }`, where the literal's fields are the
/// CALLEE's own param names, not any struct's fields). Because
/// `type_check_app` only tries the named-call spread in its argument-
/// check ERROR branch, a vacuous success silently steals every such
/// call. Confirmed live on the self-compiled compiler: `main.mo`'s
/// `compile_file_codegen { file_path := ..., output_dir := ..., ... }`
/// -- whose first param is a `String`, and `String` is an inductive
/// whose first constructor is `of_bytes (List U8)` -- compiled to
/// `alloc_constructor(18, 0)` (an empty `String.of_bytes`) applied as
/// ONE argument to a 5-arity partial shim, so `monad compile` returned
/// 1 without ever reaching codegen. Non-String params never hit this:
/// their expected type isn't a registered inductive, so the literal's
/// own check genuinely fails and the sugar fires as intended.
///
/// Returns `true` (trust the ordinary success) for everything except
/// that one shape: a non-literal argument, an EXPLICITLY annotated
/// literal (`{ ... } : StructName` -- the annotation is the author's
/// own statement of intent), an expected type that names no known
/// inductive, and a literal whose every field IS declared by the
/// expected type's own constructor.
#[terminating]
def struct_literal_arg_matches_expected (a : Term) (a_expected : Term) (scope : Scope) : Bool :=
    match named_call_fields_of a {
        Option.none => true,
        Option.some fields =>
            match type_head_name a_expected {
                Option.none => true,
                Option.some sname =>
                    let typ_mp : NamePath := NamePath.mk (List.cons sname List.empty) in
                    match scope_find_inductive typ_mp scope {
                        err _ => true,
                        ok ind =>
                            match ind {
                                Inductive.mk _ _ _ ctors _ _ =>
                                    match ctors {
                                        List.empty => true,
                                        List.cons ctor _ =>
                                            match ctor {
                                                InductConstructor.mk _ params _ =>
                                                    struct_lit_fields_all_declared fields params,
                                            }
                                    }
                            }
                    }
            }
    }

/// Every literal field name is among `params`' own declared names --
/// the "does this literal actually describe THIS constructor" test
/// `struct_literal_arg_matches_expected` needs. An empty literal
/// (`{}`) is vacuously all-declared, matching the reference's own
/// `fields.keys().all(..)`.
#[terminating]
def struct_lit_fields_all_declared (fields : List StructLitField) (params : List Param) : Bool :=
    match fields {
        List.empty => true,
        List.cons f rest =>
            match f {
                StructLitField.mk fname _ =>
                    if struct_lit_param_declares params fname
                    then struct_lit_fields_all_declared rest params
                    else false
            }
    }

#[terminating]
def struct_lit_param_declares (params : List Param) (name : Identifier) : Bool :=
    match params {
        List.empty => false,
        List.cons p rest =>
            match p {
                Param.mk pname _ _ _ _ =>
                    if id_eq pname name then true else struct_lit_param_declares rest name
            }
    }

/// Peels. This reads a call's ARGUMENT, and placement rule R3
/// (`lang/parser/lower_parse.mo`) puts a wrapper on every argument -- so
/// without this a located `f { x := 1 }` fell to `_ => Option.none`, the
/// named-call spread silently declined, and the call compiled as an
/// ordinary positional application. `slow_tests/
/// codegen_named_call_string_param_tests.mo` and
/// `codegen_named_call_field_access_tests.mo` are what caught it, once
/// located terms reached every path rather than only `compile --debug`.
def named_call_fields_of (a : Term) : Option (List StructLitField) :=
    match term_peel a {
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
/// `NamePath`, just applied to the owning inductive's instead. Used to
/// build a resolved named call's own result type (`Term.var sentinel
/// (DebugName.named ...)`), the same shape `type_check_struct_lit`
/// returns for an explicitly-annotated literal.
///
/// The `identifier_tail` strip is load-bearing post-qualification: a
/// qualified decl name reaches here as ONE segment (`prelude::Bool`),
/// so without it every type head the checker synthesizes from a
/// registered inductive carries the qualified spelling while source
/// annotations keep the bare one (`: Bool`) -- and `unify`'s exact
/// comparison then rejects the same type as a mismatch, swallowing
/// whole defs (a match arm returning a bare `false` vs the def's own
/// declared `Bool` was the live repro).
def inductive_bare_name (ind : Inductive) : Identifier :=
    match ind {
        Inductive.mk name _ _ _ _ _ =>
            match name {
                NamePath.mk ids =>
                    match list_last ids {
                        Option.some id => Identifier.id (identifier_tail id),
                        Option.none => Identifier.id "?",
                    }
            }
    }

def inductive_type_path (ind : Inductive) : NamePath :=
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

/// Every written field name must be among `params`' own declared names --
/// STRICTER than `struct_lit_build_args`'s own walk, which silently drops
/// an unmatched literal field because it only ever visits the STRUCT's
/// declared names, never the literal's.
///
/// `kind` is the construction spelling the message names ("named call",
/// "struct literal", "struct update"): the rule is one rule, but a reader
/// needs to see which of the three they wrote.
#[terminating]
def field_set_check_unknown (kind : String) (params : List Param) (fields : List StructLitField) : Result TypeError Bool :=
    match fields {
        List.empty => ok true,
        List.cons f rest =>
            match f {
                StructLitField.mk fname _ =>
                    if named_call_param_exists params fname
                    then field_set_check_unknown kind params rest
                    else err (TypeError.custom (String.concat kind (String.concat ": unknown field `" (String.concat (show_identifier fname) "`"))))
            }
    }

/// Every declared param must be covered by a literal field UNLESS it
/// carries a `:=` default, in which case omission is legal and the
/// default's own value stands in -- `struct_lit_build_args` (above)
/// already does exactly that substitution, so this check only has to
/// stop rejecting the omission.
///
/// A default can only ever be present on a STRUCT's own implicit
/// constructor: `cons_fields_to_params` (`lang/parser.mo`) rejects `:=`
/// on a bare `type` declaration's constructor, while
/// `struct_fields_to_params` (`lang/scope.mo`) keeps it. So requiring
/// every field unconditionally here did not mean "no defaults anywhere"
/// -- it meant a struct's ctor was MORE demanding than its own bare
/// literal form, which already accepted `{ w := 50 }` for a `Rect { w :
/// I64, h : I64 := 100 }`. Both spellings now agree.
///
/// A def's own named calls run this same check now
/// (`type_check_named_call_def_target`, below), so an omitted field with
/// a `:=` default is accepted on the def path on exactly these terms.
#[terminating]
def field_set_check_missing (kind : String) (params : List Param) (fields : List StructLitField) : Result TypeError Bool :=
    match params {
        List.empty => ok true,
        List.cons p rest =>
            match p {
                Param.mk pname _ _ pdefault _ =>
                    match struct_lit_find_field fields pname {
                        Option.some _ => field_set_check_missing kind rest fields,
                        Option.none => match pdefault {
                            Option.some _ => field_set_check_missing kind rest fields,
                            Option.none => err (TypeError.custom (String.concat kind (String.concat ": missing required field `" (String.concat (show_identifier pname) "`")))),
                        },
                    }
            }
    }

/// Both halves: every written name declared, every declared field covered
/// or defaulted. This is the rule a NAMED call (`P { x := 1 }`) and a bare
/// struct LITERAL (`{ x := 1 }`) share -- `type_check_struct_lit` calls it
/// too, so the two spellings cannot drift apart on what an omitted field
/// means.
def field_set_validate (kind : String) (params : List Param) (fields : List StructLitField) : Result TypeError Bool :=
    match field_set_check_unknown kind params fields {
        err e => err e,
        ok _ => field_set_check_missing kind params fields,
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
                    let con_mp : NamePath := NamePath.mk (List.cons bare_name List.empty) in
                    match scope_find_inductive_by_constructor con_mp scope {
                        Option.some ind =>
                            match find_constructor_in_inductive ind con_mp {
                                Option.none => ok Option.none,
                                Option.some ctor =>
                                    match ctor {
                                        InductConstructor.mk con_name params _ =>
                                            match field_set_validate "named call" params fields {
                                                err e => err e,
                                                ok _ =>
                                                    let args : List (Option Term) := struct_lit_build_args params fields in
                                                    let bindings : List (Pair Identifier Term) := con_own_param_bindings ind expected_type in
                                                    match check_con_args_against_params args params bindings scope local_types locals {
                                                        err e => err e,
                                                        ok elab_args =>
                                                            let mk_name : Identifier := struct_lit_con_name con_name in
                                                            let c : Con := Con.mk mk_name (inductive_type_path ind) (List.length params) elab_args in
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
                                        mk resolved_name _ _ _ _ =>
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
/// in `params`' declared order -- the def's own DECLARED parameter list
/// (`Def.params`, registered by `build_scope_def`; `def_params_of_term`
/// still recovers it for a decl that carries none) -- checks each against
/// its own declared type, then folds them into a plain curried `Term.app`
/// chain against `f` -- mirroring the reference compiler's own def-target
/// branch (`try_desugar_named_call`, `core_check.rs`): no per-field
/// type-CORRELATION machinery is needed beyond `type_check` itself, since
/// an ordinary curried application's own per-argument checking already
/// does the right thing at each layer.
///
/// Field validation is the CONSTRUCTOR path's own helpers now, over the
/// same `List Param`: `field_set_check_unknown` for the field
/// NAMES, and `named_call_def_pair_args` for the `:=` DEFAULTS. The two
/// def-side mirrors of them (`named_call_def_check_unknown_fields` and
/// `def_param_pair_exists`) are deleted rather than widened, so the two
/// paths cannot drift apart on what an omitted field means again.
def type_check_named_call_def_target (f : Term) (params : List Param) (fields : List StructLitField) (expected_type : Term) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError (Option TypedTerm) :=
    match field_set_check_unknown "named call" params fields {
        err e => err e,
        ok _ =>
            match named_call_def_pair_args params fields {
                err e => err e,
                ok arg_pairs =>
                    match named_call_def_check_args arg_pairs scope local_types locals {
                        err e => err e,
                        ok elab_args =>
                            let app_term : Term := named_call_def_fold_app f elab_args in
                            ok (Option.some (mk_typed app_term expected_type)),
                    }
            }
    }

/// Builds `(value, declared_type)` pairs in `params`' own declared order.
///
/// A param omitted from `fields` is legal exactly when it declares a `:=`
/// default, and the DEFAULT's own term then stands in for it -- the same
/// substitution `struct_lit_build_args` makes on the constructor path, so
/// `scale { p := 4 }` and `Rect { w := 50 }` are now accepted on the same
/// terms instead of a def's own spelling being the stricter one. (A default
/// is spliced in as a plain term, so it sees the CALLER's bindings, not the
/// callee's -- a default that names an earlier param is not supported, which
/// is a pre-existing property of this whole named-default design.)
///
/// That makes this function subsume the separate missing-fields pass the
/// def path used to run -- same condition, same message, same order -- so
/// `field_set_check_missing` stays the constructor path's own and
/// the only observable difference is that an omitted field with a default
/// is no longer rejected. `params` is `List Param` rather than the
/// name+type pair list this used to take because `ScopeData.def_params`
/// widened with it: the default is the whole point of the widening, and it
/// can only come from the decl (`Def.params`, populated by the parser from
/// a brace-form parameter block and lowered by `lower_parse_def`).
#[terminating]
def named_call_def_pair_args (params : List Param) (fields : List StructLitField) : Result TypeError (List (Pair Term Term)) :=
    match params {
        List.empty => ok List.empty,
        List.cons p rest =>
            match p {
                Param.mk pname ptyp _ pdefault _ =>
                    match struct_lit_find_field fields pname {
                        Option.none =>
                            match pdefault {
                                Option.none => err (TypeError.custom (String.concat "named call: missing required field `" (String.concat (show_identifier pname) "`"))),
                                Option.some value =>
                                    match named_call_def_pair_args rest fields {
                                        err e => err e,
                                        ok rest_args => ok (List.cons (Pair.pair value ptyp) rest_args),
                                    },
                            },
                        Option.some value =>
                            match named_call_def_pair_args rest fields {
                                err e => err e,
                                ok rest_args => ok (List.cons (Pair.pair value ptyp) rest_args),
                            }
                    }
            }
    }

#[terminating]
def named_call_def_check_args (args : List (Pair Term Term)) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError (List Term) :=
    match args {
        List.empty => ok List.empty,
        List.cons a rest =>
            match a {
                Pair.pair value ptyp =>
                    match type_check value ptyp scope local_types locals {
                        // The ELABORATED term, not `value`. Checking an
                        // argument is also what RESOLVES it -- a field
                        // access `f.d` only becomes a projection at its
                        // real field index here. Discarding this and
                        // folding the raw `value` back into the call (as
                        // this did) shipped the unresolved access to
                        // codegen, which compiled every one of them to
                        // field 0: `take_two { x := f.d }` read `f.a`.
                        // The constructor-target path just above always
                        // used its own `elab_args`; this is that, for an
                        // ordinary def target.
                        ok checked =>
                            match named_call_def_check_args rest scope local_types locals {
                                ok rest_terms => ok (List.cons (checked.term) rest_terms),
                                err e => err e,
                            },
                        err e => err e,
                    }
            }
    }

#[terminating]
def named_call_def_fold_app (f : Term) (args : List Term) : Term :=
    match args {
        List.empty => f,
        List.cons value rest => named_call_def_fold_app (Term.app f value) rest,
    }

/// Type check a struct-update expression (`{ base with field := value,
/// ... }`) by DESUGARING it into one single-case `match` over `base`
/// whose arm rebuilds the struct as a real `Term.con`: every declared
/// field is a binder of that arm, and each constructor argument is
/// either the update's own override value or the binder for the field it
/// did not touch.
///
/// The reference desugars the same thing per FIELD (`core/src/
/// core_check.rs`'s `desugar_struct_literals`, which clones `base` into
/// one projection `Match` per un-overridden field), and so did this --
/// which is free when `base` is a variable and a repeated CALL when it is
/// anything else. One match evaluates it once, which is what lets the
/// base be a call at all (`struct_update_base`, `lang/parser.mo`).
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
            let base_term : Term := base_tt.term in
            let base_typ : Term := base_tt.typ in
            match type_head_name base_typ {
                Option.none => struct_update_fallback base_term fields base_typ,
                Option.some sname =>
                    let typ_mp : NamePath := NamePath.mk (List.cons sname List.empty) in
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
                                                    // An override naming no declared field used
                                                    // to be dropped on the floor: the args walk
                                                    // visits declared params only, so only the
                                                    // written values it recognised were ever
                                                    // checked and `{ p with nosuch := 3 }`
                                                    // checked clean. Only the UNKNOWN half
                                                    // applies -- omitting a field is what an
                                                    // update is for.
                                                    match field_set_check_unknown "struct update" params fields {
                                                        err e => err e,
                                                        ok _ =>
                                                    let n : I64 := List.length params in
                                                    let binders : List Identifier := struct_update_binders params in
                                                    // Only the OVERRIDES are type-checked, each against
                                                    // the struct's own DECLARED field type (`params`) --
                                                    // `{ p with x := 5 }` where `p.x : String` rejects
                                                    // the mismatch, the same `check_con_args_against_
                                                    // params` reuse ordinary struct literals get. An
                                                    // untouched field needs no check: it becomes a
                                                    // binder of the wrapping match, typed by the
                                                    // constructor itself.
                                                    let bindings : List (Pair Identifier Term) := con_own_param_bindings ind base_typ in
                                                    match check_con_args_against_params (struct_update_override_args params fields) params bindings scope local_types locals {
                                                        err e => err e,
                                                        ok elab_overrides =>
                                                            let mk_name : Identifier := struct_lit_con_name con_name in
                                                            let args : List (Option Term) := struct_update_arm_args elab_overrides binders n 0 in
                                                            let body : Term := Term.con (Con.mk mk_name typ_mp n args) in
                                                            let no_fp : Option FieldPattern := Option.none in
                                                            let case_ : MatchCase := MatchCase.mk mk_name binders body no_fp (Option.some (inductive_type_path ind)) in
                                                            ok (mk_typed (Term.lit (Literal.match_ base_term (List.cons case_ List.empty))) base_typ),
                                                    }
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

/// One slot per declared field: the update's own override term where it
/// names that field, `Option.none` otherwise. `check_con_args_against_
/// params` skips a `none`, so exactly the written values get checked.
#[terminating]
def struct_update_override_args (params : List Param) (fields : List StructLitField) : List (Option Term) :=
    match params {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Param.mk pname _ _ _ _ =>
                    List.cons (struct_lit_find_field fields pname) (struct_update_override_args rest fields)
            }
    }

/// The wrapping match arm's binder names: one per declared field, PREFIXED.
///
/// The prefix is load-bearing. Codegen binds an arm's args by NAME
/// (`bind_match_fields`, `lang/codegen/emit.mo`), so a binder spelled like
/// the field would shadow a same-named outer variable inside the arm --
/// and `{ r with status := status }`, a parameter passed to the field it
/// is named after, is exactly how a struct update gets written. The
/// override terms are shifted under these binders but keep their own
/// names, so the shadowing would be silent and the value wrong. Same
/// fixed-prefix trick as `lang/parser.mo`'s `__struct_param`.
#[terminating]
def struct_update_binders (params : List Param) : List Identifier :=
    match params {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Param.mk pname _ _ _ _ =>
                    List.cons (Identifier.id (String.concat "__su_" (show_identifier pname))) (struct_update_binders rest)
            }
    }

/// The arm's constructor args, in declared order: an overridden field's
/// own elaborated term shifted under the arm's `total` binders, an
/// untouched field's binder read straight back.
///
/// `(total - 1) - idx` is the de Bruijn index of the `idx`th declared
/// field once all `total` of them are bound (last-declared = innermost =
/// index 0, this codebase's convention -- see `lang/scope.mo`'s
/// `add_constructors_go`).
///
/// ONE match over the base, not one per untouched field. The per-field
/// shape re-evaluated `base` once per field it did not touch, which is
/// free for a variable and is a repeated CALL for anything else -- and a
/// call is what the base is now allowed to be (`struct_update_base`,
/// `lang/parser.mo`).
#[terminating]
def struct_update_arm_args (overrides : List (Option Term)) (binders : List Identifier) (total : I64) (idx : I64) : List (Option Term) :=
    match overrides {
        List.empty => List.empty,
        List.cons o orest =>
            match binders {
                List.empty => List.empty,
                List.cons nm nrest =>
                    let value : Term := match o {
                        Option.some t => term_shift total t,
                        Option.none => Term.var ((total - 1) - idx) (DebugName.named nm),
                    } in
                    List.cons (Option.some value) (struct_update_arm_args orest nrest total (I64.add idx 1))
            }
    }

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
/// scope_add_instances_to_group sd.instances cname [ins] }`:
/// `sd.instances` -- field index 2 of `ScopeData` -- compiled to read
/// field 0 instead, handing the registration helper an unrelated
/// `HashMap` to recurse into as if it were a `List ScopeInstance`) and
/// independently via a
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
                                ok rest_elab => ok (List.cons (Option.some (tt.term)) rest_elab),
                            },
                    }
            }
    }

/// Zip each present argument against the constructor's own declared
/// params, positionally, checking each present arg against its param's
/// declared type -- with `bindings` (`con_own_param_bindings`) applied
/// first, so a PARAMETERIZED type's param type (`run : M (Result E A)`
/// for `ResultT.mk`) is checked against what `expected_type` already
/// said `E`/`M`/`A` are, not their bare, still-abstract names. If `args`
/// somehow outlasts `params` (shouldn't happen once `type_check_con`'s
/// own arity check has already run, but stay defensive rather than
/// silently skipping the overflow), the remaining args fall back to
/// `check_con_args_untyped`. Returns the ELABORATED args -- see
/// `check_con_args_untyped`'s own doc comment just above for why.
#[terminating]
def check_con_args_against_params (args : List (Option Term)) (params : List Param) (bindings : List (Pair Identifier Term)) (scope : Scope) (local_types : List Term) (locals : LocalScope) : Result TypeError (List (Option Term)) :=
    match args {
        List.empty => ok List.empty,
        List.cons a rest =>
            match params {
                List.empty => check_con_args_untyped args scope local_types locals,
                List.cons p prest =>
                    match a {
                        Option.none =>
                            match check_con_args_against_params rest prest bindings scope local_types locals {
                                err e => err e,
                                ok rest_elab => ok (List.cons Option.none rest_elab),
                            },
                        Option.some term =>
                            match p {
                                Param.mk _ ptyp _ _ _ =>
                                    match type_check term ptyp scope local_types locals {
                                        err e => err e,
                                        ok tt =>
                                            match check_con_args_against_params rest prest bindings scope local_types locals {
                                                err e => err e,
                                                ok rest_elab => ok (List.cons (Option.some (tt.term)) rest_elab),
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
// minimal single-constructor `Box` inductive (one param, declared at sort
// level 2) directly into a fresh `Scope`, mirroring
// `lang/tests/scope_tests.mo`/`types_tests.mo`'s own hand-built-fixture
// convention. The param's argument is a SORT specifically (not a
// literal/free-var) because `type_check_sort_full` is one of the
// few leaf checkers that actually compares against `expected_type`
// (see `type_check_ntv`'s own doc comment above: most leaf cases here
// just infer and return, ignoring `expected_type` — a literal argument
// would trivially "pass" any declared param type, proving nothing).

def box_module_path : ModulePath := ModulePath.mk (List.cons (Identifier.id "Box") List.empty)

def box_ctor_path : NamePath := NamePath.mk (List.cons (Identifier.id "Box") List.empty)

/// A constructor's registered path is its BARE name -- what
/// `build_scope_struct` (`lang/scope.mo`) and the parser both write.
/// This fixture used to register `[Box, box]`, which only ever matched
/// `type_check_con`'s own (wrong) `typ_name ++ [cname]` lookup key, so
/// the two agreed with each other and with nothing else.
def box_ctor_bare_path : NamePath := NamePath.mk (List.cons (Identifier.id "box") List.empty)

def box_param : Param := Param.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 2)) Multiplicity.many Option.none List.empty

def box_constructor : InductConstructor := InductConstructor.mk box_ctor_bare_path [box_param] (Term.sort (SortLevel.concrete 3))

def box_inductive : Inductive := Inductive.mk box_ctor_path List.empty (Term.sort (SortLevel.concrete 3)) [box_constructor] List.empty Visibility.package_private

def box_scope : Scope := {
    module_id := box_module_path,
    scope := scope_data_add_inductive scope_data_empty box_inductive,
    parent := Option.none,
    incomplete_match_ok := false,
}

#[test]
def test_type_check_con_valid_arg_ok : Bool :=
    let arg : Term := Term.sort (SortLevel.concrete 1) in
    let c : Con := Con.mk (Identifier.id "box") box_ctor_path 1 (List.cons (Option.some arg) List.empty) in
    match type_check_con c Term.hole box_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_type_check_con_wrong_arg_type_rejected : Bool :=
    // `x`'s declared param type is a sort at level 2 — a sort at level 5
    // is NOT a valid inhabitant (`type_check_sort_full`'s own
    // `expected_level < level` branch), so this must be rejected.
    let bad_arg : Term := Term.sort (SortLevel.concrete 5) in
    let c : Con := Con.mk (Identifier.id "box") box_ctor_path 1 (List.cons (Option.some bad_arg) List.empty) in
    match type_check_con c Term.hole box_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

#[test]
def test_type_check_con_wrong_arity_rejected : Bool :=
    // `box` declares exactly 1 param — claiming 2 must be rejected
    // regardless of `args`' own content.
    let arg : Term := Term.sort (SortLevel.concrete 1) in
    let c : Con := Con.mk (Identifier.id "box") box_ctor_path 2 (List.cons (Option.some arg) (List.cons (Option.some arg) List.empty)) in
    match type_check_con c Term.hole box_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

#[test]
def test_type_check_con_unknown_constructor_rejected : Bool :=
    let arg : Term := Term.sort (SortLevel.concrete 1) in
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
    let unknown_typ : NamePath := NamePath.mk (List.cons (Identifier.id "NoSuchType") List.empty) in
    let good_arg : Term := Term.sort (SortLevel.concrete 1) in
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

def point_module_path : ModulePath := ModulePath.mk (List.cons (Identifier.id "Point") List.empty)

def point_type_path : NamePath := NamePath.mk (List.cons (Identifier.id "Point") List.empty)

def point_mk_path : NamePath := NamePath.mk (List.cons (Identifier.id "mk") List.empty)

def point_x_param : Param := Param.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 2)) Multiplicity.many Option.none List.empty

def point_y_param : Param := Param.mk (Identifier.id "y") (Term.sort (SortLevel.concrete 2)) Multiplicity.many Option.none List.empty

def point_params : List Param := List.cons point_x_param (List.cons point_y_param List.empty)

def point_constructor : InductConstructor := InductConstructor.mk point_mk_path point_params Term.hole

def point_inductive : Inductive := Inductive.mk point_type_path List.empty Term.hole (List.cons point_constructor List.empty) List.empty Visibility.package_private

def point_scope : Scope := {
    module_id := point_module_path,
    scope := scope_data_add_inductive scope_data_empty point_inductive,
    parent := Option.none,
    incomplete_match_ok := false,
}

def point_type_ref : Term := Term.var sentinel (DebugName.named (Identifier.id "Point"))

#[test]
def test_type_check_struct_lit_self_annotated_ok : Bool :=
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 1)) in
    let f2 : StructLitField := StructLitField.mk (Identifier.id "y") (Term.sort (SortLevel.concrete 1)) in
    let fields : List StructLitField := List.cons f1 (List.cons f2 List.empty) in
    let type_name : Option Term := Option.some point_type_ref in
    match type_check_struct_lit fields type_name Term.hole point_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_type_check_struct_lit_from_expected_type_ok : Bool :=
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 1)) in
    let f2 : StructLitField := StructLitField.mk (Identifier.id "y") (Term.sort (SortLevel.concrete 1)) in
    let fields : List StructLitField := List.cons f1 (List.cons f2 List.empty) in
    let no_annotation : Option Term := Option.none in
    match type_check_struct_lit fields no_annotation point_type_ref point_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_type_check_struct_lit_no_annotation_no_expected_rejected : Bool :=
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 1)) in
    let fields : List StructLitField := List.cons f1 List.empty in
    let no_annotation : Option Term := Option.none in
    match type_check_struct_lit fields no_annotation Term.hole point_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

#[test]
def test_type_check_struct_lit_wrong_field_type_rejected : Bool :=
    // `x`'s declared param type is a sort at level 2 -- a sort at level 5
    // is not a valid inhabitant, same reasoning as
    // `test_type_check_con_wrong_arg_type_rejected` above.
    let bad_f : StructLitField := StructLitField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 5)) in
    let fields : List StructLitField := List.cons bad_f List.empty in
    let type_name : Option Term := Option.some point_type_ref in
    match type_check_struct_lit fields type_name Term.hole point_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

#[test]
def test_type_check_struct_lit_missing_field_rejected : Bool :=
    // Only `x` provided, `y` absent and not defaulted -- an ERROR since
    // 2026-10-28 (both compilers): the hole the omission left is what
    // `lower_sparse_args` truncates an allocation at.
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 1)) in
    let fields : List StructLitField := List.cons f1 List.empty in
    let type_name : Option Term := Option.some point_type_ref in
    match type_check_struct_lit fields type_name Term.hole point_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
    }

// --- Regression: the shape codegen's own struct-literal desugar produces ---
//
// `desugar_struct_lit_con` (`lang/codegen/emit.mo`) rewrites an annotated
// literal to `Con.mk <bare ctor> <type path> n args` and leaves the per-arg
// CHECK to the elaborate pass that follows it. That pass is `type_check_con`,
// and it used to look the constructor up under `typ_name ++ [cname]` --
// `[Point, mk]`, a path nothing registers -- so EVERY def holding an
// annotated struct literal failed to elaborate, `elaborate_module_decls_
// best_effort` kept it un-elaborated, and its field accesses reached codegen
// as the parser's one-binder `field_access_chain` match, which
// `bind_match_fields` reads at index 0. That is the whole of
// `plans/implementations/2026-10-03-any-boxed-struct-reconstruction-corrupts-
// sibling-field.md` and the `if s.bool_field` segfault filed beside it: a
// non-zero field read silently returned field 0.

/// The desugared shape itself must elaborate. Fails on the pre-fix lookup.
#[test]
def test_type_check_con_struct_mk_bare_path_ok : Bool :=
    let arg : Term := Term.sort (SortLevel.concrete 1) in
    let args : List (Option Term) := [Option.some arg, Option.some arg] in
    let c : Con := Con.mk (Identifier.id "mk") point_type_path 2 args in
    match type_check_con c Term.hole point_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

/// The first case's binder count of a `match` sitting in one of a `Con`'s
/// args, or -1 if nothing there is that shape. The number IS the bug: the
/// parser builds one binder for `p.y`, and only elaboration expands it to
/// the struct's declared field count, which is what makes `monad_get_field`
/// read index 1 rather than 0.
def con_first_arg_case_arity (t : Term) : I64 :=
    match t {
        Term.con c =>
            match c {
                Con.mk _ _ _ args =>
                    first_filled_case_arity args,
            },
        _ => -1,
    }

/// The first FILLED slot's arity -- `struct_lit_build_args` leaves an
/// omitted field as `Option.none`, so the interesting arg is rarely slot 0.
def first_filled_case_arity (args : List (Option Term)) : I64 :=
    match args {
        List.cons a rest =>
            match a {
                Option.some inner => match_first_case_arity inner,
                Option.none => first_filled_case_arity rest,
            },
        List.empty => -1,
    }

def match_first_case_arity (t : Term) : I64 :=
    match t {
        Term.lit l =>
            match l {
                Literal.match_ _ cases =>
                    match cases {
                        List.cons c _ => match c { MatchCase.mk _ cargs _ _ _ => List.length cargs },
                        List.empty => -1,
                    },
                _ => -1,
            },
        _ => -1,
    }

/// A field read inside the desugared `Con` must come back EXPANDED to the
/// struct's declared field count (2 for `Point`), not the single binder the
/// parser wrote. Pre-fix this arity was 1 and the read compiled to field 0.
#[test]
def test_type_check_con_elaborates_a_field_access_arg : Bool :=
    let subject : Term := Term.var 0 (DebugName.named (Identifier.id "p")) in
    let read_y : Term := field_access_chain subject [Identifier.id "y"] in
    // `y`'s slot filled, `x`'s left `Option.none` -- the sparse shape
    // `struct_lit_build_args` produces for an omitted field, and the arity
    // still has to be the struct's own 2.
    let args : List (Option Term) := [Option.none, Option.some read_y] in
    let c : Con := Con.mk (Identifier.id "mk") point_type_path 2 args in
    let locals : LocalScope := prepend_typed_local_vars [Identifier.id "p"] [point_type_ref] empty_locals in
    match type_check_con c Term.hole point_scope [point_type_ref] locals {
        ok tt => I64.beq (con_first_arg_case_arity tt.term) 2,
        err _ => false,
    }

// --- Regression: a struct update is ONE match over its base ---------
//
// The desugaring used to build one projection `match base { mk a b => b }`
// per un-overridden field, cloning `base` into each -- free for a variable
// and a repeated CALL for anything else, which is what the base is now
// allowed to be. These rows pin the shape rather than a value: a single
// match whose scrutinee is the base IS the "evaluated once" property, and
// no program's output can show it.

/// The scrutinee of the elaborated term, or `Option.none` if it is not a
/// one-case match at all.
def struct_update_scrutinee (t : Term) : Option Term :=
    match t {
        Term.lit l =>
            match l {
                Literal.match_ scrut cases =>
                    match cases {
                        List.cons _ rest =>
                            match rest {
                                List.empty => Option.some scrut,
                                List.cons _ _ => Option.none,
                            },
                        List.empty => Option.none,
                    },
                _ => Option.none,
            },
        _ => Option.none,
    }

def point_update_term : Result TypeError TypedTerm :=
    let subject : Term := Term.var 0 (DebugName.named (Identifier.id "p")) in
    let override_ : StructLitField := StructLitField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 1)) in
    let locals : LocalScope := prepend_typed_local_vars [Identifier.id "p"] [point_type_ref] empty_locals in
    type_check_struct_update subject [override_] Term.hole point_scope [point_type_ref] locals

/// Is this term the bound variable at `idx`?
def term_is_bound_at (t : Term) (idx : I64) : Bool :=
    match t {
        Term.var i _dbg => I64.beq i idx,
        _ => false,
    }

/// One match, and its scrutinee is the base -- `Point` has an untouched
/// field (`y`), which is exactly what the old shape cloned the base for.
#[test]
def test_struct_update_is_one_match_over_the_base : Bool :=
    match point_update_term {
        ok tt =>
            match struct_update_scrutinee tt.term {
                Option.some scrut => term_is_bound_at scrut 0,
                Option.none => false,
            },
        err _ => false,
    }

/// The arm binds one binder per declared field, so the untouched field can
/// be read back from a binder instead of from a second look at the base.
#[test]
def test_struct_update_arm_binds_every_field : Bool :=
    match point_update_term {
        ok tt => I64.beq (match_first_case_arity tt.term) 2,
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
def test_type_check_struct_lit_extra_unknown_field_rejected : Bool :=
    // A literal field with no matching declared param was silently dropped
    // before 2026-10-28; it is an ERROR now, on both compilers.
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 1)) in
    let f2 : StructLitField := StructLitField.mk (Identifier.id "y") (Term.sort (SortLevel.concrete 1)) in
    let extra : StructLitField := StructLitField.mk (Identifier.id "z_not_a_field") (Term.sort (SortLevel.concrete 1)) in
    let fields : List StructLitField := List.cons f1 (List.cons f2 (List.cons extra List.empty)) in
    let type_name : Option Term := Option.some point_type_ref in
    match type_check_struct_lit fields type_name Term.hole point_scope empty_local_types empty_locals {
        ok _ => false,
        err _ => true,
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

def solo_module_path : ModulePath := ModulePath.mk (List.cons (Identifier.id "Solo") List.empty)

def solo_type_path : NamePath := NamePath.mk (List.cons (Identifier.id "Solo") List.empty)

def solo_mk_path : NamePath := NamePath.mk (List.cons (Identifier.id "mk") List.empty)

def solo_n_param : Param := Param.mk (Identifier.id "n") (Term.sort (SortLevel.concrete 2)) Multiplicity.many Option.none List.empty

def solo_constructor : InductConstructor := InductConstructor.mk solo_mk_path (List.cons solo_n_param List.empty) Term.hole

def solo_inductive : Inductive := Inductive.mk solo_type_path List.empty Term.hole (List.cons solo_constructor List.empty) List.empty Visibility.package_private

def solo_scope : Scope := {
    module_id := solo_module_path,
    scope := scope_data_add_inductive scope_data_empty solo_inductive,
    parent := Option.none,
    incomplete_match_ok := false,
}

def solo_mk_var : Term := Term.var sentinel (DebugName.named (Identifier.id "mk"))

#[test]
def test_type_check_named_call_multi_field_reordered : Bool :=
    // Fields given in the OPPOSITE order from `point_params`' own
    // declaration (y then x) -- order-independence is the whole point.
    let fy : StructLitField := StructLitField.mk (Identifier.id "y") (Term.sort (SortLevel.concrete 1)) in
    let fx : StructLitField := StructLitField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 1)) in
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
    let f1 : StructLitField := StructLitField.mk (Identifier.id "n") (Term.sort (SortLevel.concrete 1)) in
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
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 1)) in
    let f2 : StructLitField := StructLitField.mk (Identifier.id "y") (Term.sort (SortLevel.concrete 1)) in
    let bad : StructLitField := StructLitField.mk (Identifier.id "z_not_a_field") (Term.sort (SortLevel.concrete 1)) in
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
    // (see `field_set_validate`'s own doc comment), not a gap.
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 1)) in
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
    let fy : StructLitField := StructLitField.mk (Identifier.id "y") (Term.sort (SortLevel.concrete 1)) in
    let fx : StructLitField := StructLitField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 1)) in
    let fields : List StructLitField := List.cons fy (List.cons fx List.empty) in
    let arg : Term := Term.lit (Literal.struct_lit fields Option.none) in
    match type_check_app point_mk_var arg Term.hole point_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

// --- Tests for type_check_named_call's def-target branch (Phase 6 of
// plans/implementations/named-field-construction.md) ---
//
// Hand-built `Def` (name "scale", two params "factor"/"p" at sort level 2,
// body a sort at level 1 -- same sort-level convention
// `box_scope`/`point_scope` use above, and for the same reason: only a
// SORT argument actually exercises `type_check_sort_full`'s
// own comparison against a declared param type, unlike a literal/
// free-var argument which would trivially "pass" any type), registered
// via the REAL `build_scope_def` (not a hand-assembled `ScopeData`
// literal) so this exercises the actual `def_params_of_term`/`scope_
// data_add_def_params` registration path, not just its consumer.

def scale_module_path : ModulePath := ModulePath.mk (List.cons (Identifier.id "scale") List.empty)

def scale_def_name : NamePath := NamePath.mk (List.cons (Identifier.id "scale") List.empty)

def scale_def_body : Term :=
    Term.lam (binder_named (Identifier.id "factor")) (Term.sort (SortLevel.concrete 2))
        (Term.lam (binder_named (Identifier.id "p")) (Term.sort (SortLevel.concrete 2)) (Term.sort (SortLevel.concrete 1)))

def scale_def : Def := {
    name := scale_def_name,
    typ := Term.hole,
    term := scale_def_body,
    constraints := List.empty,
    attrs := List.empty,
    vis := Visibility.package_private,
    params := List.empty,
}

def scale_scope : Scope := {
    module_id := scale_module_path,
    scope := build_scope_def scale_def scale_module_path scope_data_empty,
    parent := Option.none,
    incomplete_match_ok := false,
}

def scale_var : Term := Term.var sentinel (DebugName.named (Identifier.id "scale"))

#[test]
def test_type_check_named_call_def_target_reordered : Bool :=
    // Fields given in the OPPOSITE order from `scale_def_body`'s own
    // declaration (p then factor).
    let fp : StructLitField := StructLitField.mk (Identifier.id "p") (Term.sort (SortLevel.concrete 1)) in
    let ff : StructLitField := StructLitField.mk (Identifier.id "factor") (Term.sort (SortLevel.concrete 1)) in
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
    // `factor`'s declared param type is a sort at level 2 -- a sort at
    // level 5 is not a valid inhabitant, same reasoning as the constructor-
    // target `wrong_arg_type`/`wrong_field_type` tests above.
    let fp : StructLitField := StructLitField.mk (Identifier.id "p") (Term.sort (SortLevel.concrete 1)) in
    let ff : StructLitField := StructLitField.mk (Identifier.id "factor") (Term.sort (SortLevel.concrete 5)) in
    let fields : List StructLitField := List.cons fp (List.cons ff List.empty) in
    match type_check_named_call scale_var fields Term.hole scale_scope empty_local_types empty_locals {
        err _ => true,
        ok _ => false,
    }

#[test]
def test_type_check_named_call_def_target_unknown_field_is_an_error : Bool :=
    let fp : StructLitField := StructLitField.mk (Identifier.id "p") (Term.sort (SortLevel.concrete 1)) in
    let ff : StructLitField := StructLitField.mk (Identifier.id "factor") (Term.sort (SortLevel.concrete 1)) in
    let bad : StructLitField := StructLitField.mk (Identifier.id "not_a_param") (Term.sort (SortLevel.concrete 1)) in
    let fields : List StructLitField := List.cons fp (List.cons ff (List.cons bad List.empty)) in
    match type_check_named_call scale_var fields Term.hole scale_scope empty_local_types empty_locals {
        err _ => true,
        ok _ => false,
    }

#[test]
def test_type_check_named_call_def_target_missing_field_is_an_error : Bool :=
    // No default mechanism exists for ordinary `lang/` def params --
    // omitting `p` must always be an error.
    let ff : StructLitField := StructLitField.mk (Identifier.id "factor") (Term.sort (SortLevel.concrete 1)) in
    let fields : List StructLitField := List.cons ff List.empty in
    match type_check_named_call scale_var fields Term.hole scale_scope empty_local_types empty_locals {
        err _ => true,
        ok _ => false,
    }

#[test]
def test_type_check_app_resolves_def_target_named_call_end_to_end : Bool :=
    // Full `type_check_app` dispatch: `scale { p := .., factor := .. }`
    // parses as `App(Var(scale), StructLit)`.
    let fp : StructLitField := StructLitField.mk (Identifier.id "p") (Term.sort (SortLevel.concrete 1)) in
    let ff : StructLitField := StructLitField.mk (Identifier.id "factor") (Term.sort (SortLevel.concrete 1)) in
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
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 1)) in
    let fields : List StructLitField := List.cons f1 List.empty in
    match type_check_struct_update point_var fields Term.hole point_scope point_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_type_check_struct_update_result_type_is_base_type : Bool :=
    let fields : List StructLitField := List.empty in
    match type_check_struct_update point_var fields Term.hole point_scope point_local_types empty_locals {
        ok tt => match type_head_name (tt.typ) {
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
/// term must be something `lang/src/codegen/emit.mo` actually compiles --
/// NOT a bare `Term.lit (Literal.struct_update ...)`, which
/// `compile_lit_ir` has no real codegen for and which
/// `type_check_struct_update` ALWAYS produced before that fix.
///
/// The shape is now one `match` over the base whose arm rebuilds the
/// struct as a `Term.con`; it was a bare `Term.con` with a projection
/// `match` per untouched field until the base stopped being restricted to
/// a variable (see `test_struct_update_is_one_match_over_the_base`). Both
/// shapes are codegen-proven; this row asks only that it is not the
/// un-desugared literal.
#[test]
def test_type_check_struct_update_desugars_for_codegen : Bool :=
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 1)) in
    let fields : List StructLitField := List.cons f1 List.empty in
    match type_check_struct_update point_var fields Term.hole point_scope point_local_types empty_locals {
        ok tt => match struct_update_arm_body tt.term {
            Option.some body => match body { Term.con _ => true, _ => false },
            Option.none => false,
        },
        err _ => false,
    }

/// The overridden field (`x`) becomes the override's own value (arg 0,
/// matching `point_params`' declared order `x`, `y`); the UNCHANGED field
/// (`y`) comes back as the arm's own BINDER for it -- not the override
/// value, and not left blank.
#[test]
def test_type_check_struct_update_unchanged_field_is_its_binder : Bool :=
    let f1 : StructLitField := StructLitField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 1)) in
    let fields : List StructLitField := List.cons f1 List.empty in
    match type_check_struct_update point_var fields Term.hole point_scope point_local_types empty_locals {
        ok tt => match struct_update_arm_body tt.term {
            Option.some body => match body {
                Term.con c => match c {
                    Con.mk _name _typ_name _arity args => match args {
                        List.cons x_arg rest => match rest {
                            // `y` is the LAST declared field, so its
                            // binder is the innermost one: index 0.
                            List.cons y_arg _ => is_type_arg x_arg && is_bound_arg y_arg 0,
                            List.empty => false,
                        },
                        List.empty => false,
                    },
                },
                _ => false,
            },
            Option.none => false,
        },
        err _ => false,
    }

/// The body of the single arm of a desugared struct update.
#[partial]
def struct_update_arm_body (t : Term) : Option Term :=
    match t {
        Term.lit l => match l {
            Literal.match_ _scrut cases => match cases {
                List.cons c _ => match c { MatchCase.mk _n _a body _fp _tn => Option.some body },
                List.empty => Option.none,
            },
            _ => Option.none,
        },
        _ => Option.none,
    }

#[partial]
def is_type_arg (arg : Option Term) : Bool :=
    match arg {
        Option.some t => match t {
            // A sort IS a type.
            Term.sort _ => true,
            _ => false,
        },
        Option.none => false,
    }

#[partial]
def is_bound_arg (arg : Option Term) (idx : I64) : Bool :=
    match arg {
        Option.some t => term_is_bound_at t idx,
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
        ok tt => match tt.term {
            Term.lit l => match l { Literal.struct_update _ _ => true, _ => false },
            _ => false,
        },
        err _ => false,
    }

// --- Regression: struct-update overrides are checked against the
// struct's own DECLARED field type, not blindly accepted (`Term.hole`)
// ---
//
// `point_scope`'s own `x`/`y` fields are typed as a bare sort at level 2
// (deliberately permissive so the OTHER struct-update tests above can
// freely use a bare sort as a stand-in override value) -- too permissive
// to demonstrate a real rejection via cumulativity. This
// fixture instead gives `Wrap`'s one field a CONCRETE, non-sort type
// (`Point`, reusing `point_type_ref`), so an override of a different,
// structurally-unrelated shape (a bare sort) has somewhere real to
// conflict with.

def wrap_module_path : ModulePath := ModulePath.mk (List.cons (Identifier.id "Wrap") List.empty)

def wrap_type_path : NamePath := NamePath.mk (List.cons (Identifier.id "Wrap") List.empty)

def wrap_mk_path : NamePath := NamePath.mk (List.cons (Identifier.id "mk") List.empty)

def wrap_v_param : Param := Param.mk (Identifier.id "v") point_type_ref Multiplicity.many Option.none List.empty

def wrap_constructor : InductConstructor := InductConstructor.mk wrap_mk_path (List.cons wrap_v_param List.empty) Term.hole

def wrap_inductive : Inductive := Inductive.mk wrap_type_path List.empty Term.hole (List.cons wrap_constructor List.empty) List.empty Visibility.package_private

def wrap_scope : Scope := {
    module_id := wrap_module_path,
    scope := scope_data_add_inductive scope_data_empty wrap_inductive,
    parent := Option.none,
    incomplete_match_ok := false,
}

def wrap_local_types : List Term := List.cons (Term.var sentinel (DebugName.named (Identifier.id "Wrap"))) empty_local_types

def wrap_var : Term := Term.var 0 (DebugName.named (Identifier.id "w"))

#[test]
def test_type_check_struct_update_rejects_mismatched_field_type : Bool :=
    // `v : Point`, overridden with a bare sort --
    // structurally unrelated to a concrete `Point` reference, so this
    // must be REJECTED. Before this fix (`struct_update_check_fields`
    // checking every override against `Term.hole`, i.e. "anything
    // goes"), this incorrectly returned `ok`.
    let f1 : StructLitField := StructLitField.mk (Identifier.id "v") (Term.sort (SortLevel.concrete 1)) in
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

// --- Tests for extract_pi_ret's type-variable instantiation ---

/// The `Scope` these three tests resolve against, deliberately with
/// NOTHING registered: `solve_typevars` refuses to record a param-side
/// free var whose name RESOLVES (`is_scope_type_name` -- a free var in
/// a registered `Def.typ` is either the def's implicit type parameter or
/// a concrete type name, and resolution is the only discriminator), so
/// registering `A` here would make every assertion below vacuous.
def pi_ret_test_scope : Scope := {
    module_id := ModulePath.mk (List.cons (Identifier.id "PiRetTest") List.empty),
    scope := scope_data_empty,
    parent := Option.none,
    incomplete_match_ok := false,
}

/// `FromListLiteral.cons`'s promoted signature, exactly as
/// `promote_methods` (`lang/scope.mo`) registers it -- `Def.typ` copied
/// through unchanged, so the implicit `A` is still a free `sentinel`
/// var: there is no `forall` wrapper at this point in the pipeline.
def cons_promoted_sig : Term :=
    let a : Term := Term.var sentinel (DebugName.named (Identifier.id "A")) in
    let list_a : Term := Term.app (Term.var sentinel (DebugName.named (Identifier.id "List"))) a in
    Term.pi binder_anon a (Term.pi binder_anon list_a list_a)

/// `FromListLiteral_List_empty`'s promoted signature (`List A`) -- the
/// other shape the failing case goes through, where the type variable
/// sits INSIDE the first (and only) parameter rather than being it.
def empty_promoted_sig : Term :=
    let a : Term := Term.var sentinel (DebugName.named (Identifier.id "A")) in
    Term.pi binder_anon (Term.app (Term.var sentinel (DebugName.named (Identifier.id "List"))) a) (Term.app (Term.var sentinel (DebugName.named (Identifier.id "List"))) a)

/// `List U8`, the type `cons`'s first argument infers to at the failing
/// site (`Sha256.hash_bytes`'s `List.flatten [unpack_word a, ...]`).
def list_u8_typ : Term :=
    Term.app (Term.var sentinel (DebugName.named (Identifier.id "List"))) (Term.var sentinel (DebugName.named (Identifier.id "U8")))

def pi_arg_of (t : Term) : Term :=
    match t {
        Term.pi _ a _ => a,
        _ => Term.hole,
    }

def pi_ret_of (t : Term) : Term :=
    match t {
        Term.pi _ _ r => r,
        _ => Term.hole,
    }

def app_arg_of (t : Term) : Term :=
    match t {
        Term.app _ a => a,
        _ => Term.hole,
    }

def head_is (t : Term) (s : String) : Bool :=
    match type_head_name t {
        Option.some id => id_eq id (Identifier.id s),
        Option.none => false,
    }

/// `extract_pi_ret` against one of the promoted signatures above,
/// applied to an argument of type `a_typ`. `f_term`/`a_term` are holes:
/// they are only ever read on the `is_hole pi_ret` path, and `pi_ret`
/// here is a real one. Reads `tt.typ` through a helper rather than
/// inline -- `#[test]` defs must not carry a direct field access (see
/// AGENTS.md).
def run_extract_pi_ret (sig : Term) (a_typ : Term) : Result TypeError TypedTerm :=
    extract_pi_ret Term.hole Term.hole sig a_typ Term.hole pi_ret_test_scope empty_local_types empty_locals

def extract_pi_ret_result_typ (r : Result TypeError TypedTerm) : Term :=
    match r {
        ok tt => tt.typ,
        err _ => Term.hole,
    }

#[test]
def test_extract_pi_ret_instantiates_typevars_from_argument : Bool :=
    // The whole remaining chain is rewritten, not just the final
    // return: `pi_arg` and `pi_ret` each go from `List A` to
    // `List (List U8)`, so peeling one pi and two apps lands on `U8`.
    // Before this fix the substitution did not exist at all and both
    // halves were still `List A` (peeling to the bare var `A`).
    let typ : Term := extract_pi_ret_result_typ (run_extract_pi_ret cons_promoted_sig list_u8_typ) in
    head_is (app_arg_of (app_arg_of (pi_arg_of typ))) "U8"
    && head_is (app_arg_of (app_arg_of (pi_ret_of typ))) "U8"

#[test]
def test_extract_pi_ret_instantiates_inside_an_applied_param : Bool :=
    // The other variable position: `List A -> List A`, where `A` is
    // nested inside the parameter rather than being it -- and where the
    // peeled result IS the return type (`List A`), not a remaining
    // chain, so `pi_arg_of` does not apply here. One app-peel from that
    // reaches `U8`: `List U8`, not `A`.
    let typ : Term := extract_pi_ret_result_typ (run_extract_pi_ret empty_promoted_sig list_u8_typ) in
    head_is (app_arg_of typ) "U8"

#[test]
def test_extract_pi_ret_hole_argument_leaves_signature_alone : Bool :=
    // The negative control for the gate this reuses: a `Term.hole`
    // argument carries no type information, so nothing may be recorded
    // and the signature must come back untouched -- still `List A`.
    // Recording a hole here is the poisoning shape `solve_typevars`'s
    // own doc comment describes.
    let typ : Term := extract_pi_ret_result_typ (run_extract_pi_ret cons_promoted_sig Term.hole) in
    head_is (app_arg_of (pi_arg_of typ)) "A"

#[test]
def test_extract_pi_ret_mismatched_shape_leaves_signature_alone : Bool :=
    // Same gate from the other side: the parameter is an applied shape
    // (`List A`) and the argument is not an application at all (a bare
    // sort), so the walk stops without recording and the return comes
    // back untouched -- still `List A`.
    let typ : Term := extract_pi_ret_result_typ (run_extract_pi_ret empty_promoted_sig (Term.sort (SortLevel.concrete 1))) in
    head_is (app_arg_of typ) "A"

// --- Tests for named-call field validation ---
//
// A `Rect { w : I64, h : I64 := 100 }`-shaped fixture, matching what
// `struct_fields_to_params` (`lang/scope.mo`) registers for a struct
// whose second field declares a default -- the only kind of constructor
// that can carry one (`cons_fields_to_params` rejects `:=` on a bare
// `type`'s own constructor).

def rect_default_value : Term := Term.var sentinel (DebugName.named (Identifier.id "the_default"))

def rect_w_param : Param := Param.mk (Identifier.id "w") (Term.sort (SortLevel.concrete 2)) Multiplicity.many Option.none List.empty

def rect_h_param : Param := Param.mk (Identifier.id "h") (Term.sort (SortLevel.concrete 2)) Multiplicity.many (Option.some rect_default_value) List.empty

def rect_params : List Param := List.cons rect_w_param (List.cons rect_h_param List.empty)

def rect_w_field : StructLitField := StructLitField.mk (Identifier.id "w") (Term.sort (SortLevel.concrete 1))

def rect_w_only_fields : List StructLitField := List.cons rect_w_field List.empty

#[test]
def test_named_call_ctor_omitted_defaulted_field_is_accepted : Bool :=
    // `Rect { w := 1 }` -- `h` is omitted but declares a default.
    match field_set_check_missing "named call" rect_params rect_w_only_fields {
        ok _ => true,
        err _ => false,
    }

#[test]
def test_named_call_ctor_omitted_undefaulted_field_is_rejected : Bool :=
    // `Rect {}` -- `w` has no default, so it must still be required.
    match field_set_check_missing "named call" rect_params List.empty {
        ok _ => false,
        err e => match e {
            TypeError.custom msg => String.contains msg "missing required field `w`",
            _ => false,
        },
    }

#[test]
def test_struct_lit_build_args_substitutes_the_default : Bool :=
    // The other half of the acceptance above: the omitted slot must be
    // filled with the DEFAULT's own value, not left a hole. A hole is
    // not an error at this point -- `lower_sparse_args` stops at the
    // first one -- it silently truncates the allocation (see
    // `struct_lit_build_args`'s own comment on the `scope_data_empty`
    // SIGSEGV).
    match struct_lit_build_args rect_params rect_w_only_fields {
        List.cons _ rest => match rest {
            List.cons second _ => match second {
                Option.some filler => match filler {
                    Term.var _ dbg => match dbg {
                        DebugName.named id => Similar.similar id (Identifier.id "the_default"),
                        DebugName.unnamed => false,
                    },
                    _ => false,
                },
                Option.none => false,
            },
            _ => false,
        },
        _ => false,
    }
