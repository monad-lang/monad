use lib::typecheck::levels {free_level_vars, is_level_binder_kind}
use lib::types {
  Attribute, Class, ClassDef, Decl, Def, DebugName, Identifier, InductConstructor,
  Inductive, Instance, MatchCase, ModulePath, Param, Similar, SortLevel, Struct,
  Term, TypeConstraint,
  app, class_d, con, def_d, forall, hole, id, id_eq, id_member, if_, inductive_d,
  infix_d, instance_d, lam, lit, match_, mc, mk, mp, name, named, ntv, num, open_d,
  pi, scoped_open_d, sentinel, show_identifier, str, struct_d, type_, union_ids, unnamed,
  use_d, var,
}
// `HashMap` stays available via the same always-on mechanism scope.mo's
// own `use std.map {}` relies on (see the comment there for why the
// `Map`-class-instance exports must not be named explicitly).
use std::map {}
use llvm::strmap {str_map_empty, str_map_insert, str_map_lookup}


/// Collect all free type variables from a Term.
/// A free variable is a var with de Bruijn index == sentinel (-1)
/// and a named debug name that is NOT in known_names.
/// Mirrors Rust's free_vars (type.rs:1901).
def free_vars (typ : Term) (known_names : List Identifier) : List Identifier :=
    match typ {
        Term.var idx dbg =>
            match dbg {
                DebugName.named id =>
                    if I64.beq idx sentinel
                    then
                        if id_member id known_names
                        then List.empty
                        else
                            let rest : List Identifier := List.empty in
                            List.cons id rest
                    else List.empty,
                DebugName.unnamed => List.empty,
            },
        Term.lam dbg typ_ body =>
            union_ids (free_vars typ_ known_names) (free_vars body known_names),
        Term.forall dbg kind body =>
            union_ids (free_vars kind known_names) (free_vars body known_names),
        Term.pi arg ret =>
            union_ids (free_vars arg known_names) (free_vars ret known_names),
        Term.app fun_ arg =>
            union_ids (free_vars fun_ known_names) (free_vars arg known_names),
        Term.lit lit_val => match lit_val {
            Literal.str _ => List.empty,
            Literal.char _ => List.empty,
            Literal.num _ _ => List.empty,
            Literal.flt _ _ => List.empty,
            Literal.if_ one two three =>
                let a := free_vars one known_names in
                let b := free_vars two known_names in
                let ab := union_ids a b in
                let c := free_vars three known_names in
                union_ids ab c,
            Literal.match_ value cases =>
                let vv := free_vars value known_names in
                free_vars_of_cases cases known_names vv,
            Literal.struct_lit fields type_name =>
                let field_vars := free_vars_of_struct_lit_fields fields known_names in
                match type_name {
                    Option.some tn => union_ids field_vars (free_vars tn known_names),
                    Option.none => field_vars,
                },
            Literal.struct_update base fields =>
                let field_vars := free_vars_of_struct_lit_fields fields known_names in
                union_ids field_vars (free_vars base known_names),
        },
        Term.con c =>
            match c {
                Con.mk _ _ _ args => free_vars_of_opt_terms args known_names,
            },
        Term.ntv _ => List.empty,
        Term.type_ _ => List.empty,
        // A sort has no free vars.
        Term.sort _level => List.empty,
        Term.hole => List.empty,
        // A location binds nothing, so the names free under it are the
        // names free in it.
        Term.ctx _loc inner => free_vars inner known_names,
    }

/// Collect free vars from match case bodies.
def free_vars_of_cases (cases : List MatchCase) (known_names : List Identifier) (acc : List Identifier) : List Identifier :=
    match cases {
        List.cons elem rest =>
            match elem {
                MatchCase.mc _ _ body _ =>
                    let body_vars := free_vars body known_names in
                    let acc_ := union_ids acc body_vars in
                    free_vars_of_cases rest known_names acc_,
            },
        List.empty => acc,
    }

/// Collect free vars from a struct literal's fields.
def free_vars_of_struct_lit_fields (fields : List StructLitField) (known_names : List Identifier) : List Identifier :=
    match fields {
        List.cons elem rest =>
            match elem {
                StructLitField.mk _ value =>
                    let hd_vars := free_vars value known_names in
                    let rest_vars := free_vars_of_struct_lit_fields rest known_names in
                    union_ids hd_vars rest_vars,
            },
        List.empty => List.empty,
    }

/// Collect free vars from Option Term list (Con args).
def free_vars_of_opt_terms (args : List (Option Term)) (known_names : List Identifier) : List Identifier :=
    match args {
        List.cons opt rest =>
            let hd_vars := match opt {
                Option.some t => free_vars t known_names,
                Option.none => List.empty,
            } in
            let rest_vars := free_vars_of_opt_terms rest known_names in
            union_ids hd_vars rest_vars,
        List.empty => List.empty,
    }

/// Collect type variable names from a list of type constraints.
def collect_constraint_vars (constraints : List TypeConstraint) (known_names : List Identifier) : List Identifier :=
    match constraints {
        List.cons elem rest =>
            match elem {
                TypeConstraint.mk _ vars =>
                    let filtered := filter_known vars known_names in
                    let rest_vars := collect_constraint_vars rest known_names in
                    union_ids filtered rest_vars,
            },
        List.empty => List.empty,
    }

/// Filter a list of identifiers, keeping only those NOT in known_names.
def filter_known (ids : List Identifier) (known_names : List Identifier) : List Identifier :=
    match ids {
        List.cons hd rest =>
            if id_member hd known_names
            then filter_known rest known_names
            else List.cons hd (filter_known rest known_names),
        List.empty => List.empty,
    }

/// Elaborate a type by adding Forall bindings for free type variables.
/// Mirrors Rust's elaborate_type (type.rs:2860).
def elaborate_type (typ : Term) (constraints : List TypeConstraint) (known_names : List Identifier) : Term :=
    let fv := free_vars typ known_names in
    let cv := collect_constraint_vars constraints known_names in
    let all_vars := union_ids fv cv in
    // Level variables generalize the same way term-level type variables
    // do, and at the same boundary -- that is the whole reason levels
    // are name-keyed (see `lang/typecheck/levels.mo`'s header). A
    // signature mentioning `Sort u` gets a `u` binder here, so `u` is
    // bound by the def rather than dangling free.
    //
    // Minus what `typ` ALREADY binds. This function is run more than
    // once over the same type -- `registered_def_type` (`lang/scope.mo`)
    // elaborates an already-elaborated decl list, and passes
    // `collect_forall_names typ` as `known_names` precisely so
    // `wrap_forall` does not re-wrap the term variables. `free_level_vars`
    // has no `known_names` of its own, so this subtraction is that same
    // guard for the level half; without it the chain grows a duplicate
    // `forall u` on every pass.
    let lv := ids_without (free_level_vars typ) (bound_level_var_names typ) in
    wrap_level_forall (wrap_forall typ all_vars) lv

/// The level-variable names `typ`'s own `Forall` binders already bind.
/// The level half of what `known_names` does for term variables -- see
/// `elaborate_type` above for why it is needed.
///
/// Keeps walking past a term binder rather than stopping at the first
/// one: `wrap_level_forall` puts level binders outermost, so they lead
/// today, but `collect_forall_names` (`lang/scope.mo`) walks the whole
/// chain defensively for the same reason and this mirrors it.
#[partial]
def bound_level_var_names (typ : Term) : List Identifier :=
    match typ {
        Term.forall dbg kind body =>
            if is_level_binder_kind kind
            then match dbg {
                DebugName.named id =>
                    union_ids (List.cons id List.empty) (bound_level_var_names body),
                DebugName.unnamed => bound_level_var_names body,
            }
            else bound_level_var_names body,
        _ => List.empty,
    }

/// `a` less every member of `b`, order otherwise preserved. `union_ids`
/// (`lang/types.mo`) is the other direction; there is no difference
/// helper there, and this is the only caller.
#[partial]
def ids_without (a : List Identifier) (b : List Identifier) : List Identifier :=
    match a {
        List.cons hd rest =>
            if id_member hd b
            then ids_without rest b
            else List.cons hd (ids_without rest b),
        List.empty => List.empty,
    }

/// Wrap a type with a `Forall` binder for each free LEVEL variable.
///
/// Sibling of `wrap_forall` below, deliberately kept separate rather
/// than folded into it: the two bind different things and are marked
/// differently, and a caller that generalizes one must be able to not
/// generalize the other.
///
/// The binder's KIND is what distinguishes a level binder from a term
/// binder downstream -- `Term.sort (SortLevel.concrete 0)` here versus
/// `wrap_forall`'s `Term.type_ 1`. That marker is readable with
/// `sort_level_of`, and it is safe because nothing inspects a `forall`
/// binder's kind SHAPE: `type_check_forall` type-checks the kind and
/// pushes it into `local_types`, but never matches on it.
///
/// Level binders go OUTSIDE the term binders (this wraps
/// `wrap_forall`'s result), so a signature's levels are bound before the
/// types that mention them.
def wrap_level_forall (typ : Term) (lvars : List Identifier) : Term :=
    match lvars {
        List.cons hd rest =>
            let kind : Term := Term.sort (SortLevel.concrete 0) in
            Term.forall (DebugName.named hd) kind (wrap_level_forall typ rest),
        List.empty => typ,
    }

/// Wrap a type with Forall binders for each free var (in order).
def wrap_forall (typ : Term) (vars : List Identifier) : Term :=
    match vars {
        List.cons hd rest =>
            let typ_ := Term.type_ 1 in
            let forall_term := Term.forall (DebugName.named hd) typ_ (wrap_forall typ rest) in
            forall_term,
        List.empty => typ,
    }

/// Elaborate a function definition's type signature.
/// Mirrors Rust's elaborate_def (type.rs:2877).
def elaborate_def (d : Def) (known_names : List Identifier) : Def :=
    match d {
        Def.mk {name, typ, term, constraints, attrs, vis, params, ..} =>
            let elaborated_typ := elaborate_type typ constraints known_names in
            Def.mk name elaborated_typ term constraints attrs vis params,
    }

/// Elaborate an inductive type definition.
/// Mirrors Rust's elaborate_inductive (type.rs:2959).
def elaborate_inductive (ind : Inductive) (known_names : List Identifier) : Inductive :=
    match ind {
        Inductive.mk name params typ constructors attrs vis =>
            let elaborated_constructors := elaborate_constructors constructors known_names in
            Inductive.mk name params typ elaborated_constructors attrs vis,
    }

/// Elaborate a list of constructors.
def elaborate_constructors (constructors : List InductConstructor) (known_names : List Identifier) : List InductConstructor :=
    match constructors {
        List.cons hd rest =>
            let elaborated_hd := elaborate_constructor hd known_names in
            let elaborated_rest := elaborate_constructors rest known_names in
            List.cons elaborated_hd elaborated_rest,
        List.empty => List.empty,
    }

/// Elaborate a single constructor's type signature.
/// For inductives with params, those params are already bound (known).
def elaborate_constructor (con : InductConstructor) (known_names : List Identifier) : InductConstructor :=
    match con {
        InductConstructor.mk name params typ =>
            // Add the inductive's own params to known_names
            // (they are bound by the inductive's forall)
            let param_names := collect_param_names params in
            let extended_names := union_ids param_names known_names in
            let elaborated_typ := elaborate_type typ List.empty extended_names in
            InductConstructor.mk name params elaborated_typ,
    }

/// Collect identifier names from a list of params.
def collect_param_names (params : List Param) : List Identifier :=
    match params {
        List.cons param rest =>
            match param {
                Param.mk name _ _ _ _ => List.cons name (collect_param_names rest),
            },
        List.empty => List.empty,
    }

/// Elaborate a class definition.
def elaborate_class (cls : Class) (known_names : List Identifier) : Class :=
    match cls {
        Class.mk name params constraints methods vis =>
            let param_names := collect_param_names params in
            let extended_names := union_ids param_names known_names in
            let elaborated_methods := elaborate_class_defs methods extended_names in
            Class.mk name params constraints elaborated_methods vis,
    }

/// Elaborate a list of class method definitions.
def elaborate_class_defs (methods : List ClassDef) (known_names : List Identifier) : List ClassDef :=
    match methods {
        List.cons hd rest =>
            let elaborated_hd := elaborate_class_def hd known_names in
            let elaborated_rest := elaborate_class_defs rest known_names in
            List.cons elaborated_hd elaborated_rest,
        List.empty => List.empty,
    }

/// Elaborate a single class method definition's type signature.
def elaborate_class_def (m : ClassDef) (known_names : List Identifier) : ClassDef :=
    match m {
        ClassDef.mk name typ default =>
            let elaborated_typ := elaborate_type typ List.empty known_names in
            ClassDef.mk name elaborated_typ default,
    }

/// Elaborate an instance definition.
/// Instance types are already concrete — we just pass through.
def elaborate_instance (ins : Instance) (known_names : List Identifier) : Instance :=
    ins

/// Elaborate a struct definition.
def elaborate_struct (s : Struct) (known_names : List Identifier) : Struct :=
    s

/// Extract an identifier from a ModulePath if it has exactly one segment.
/// A single-segment decl NAME (`name` fields on `Def`/`Inductive` are
/// `NamePath`s since the qualified-names split) collapses to that one
/// `Identifier`; a multi-segment or empty name yields `Option.none`.
def np_to_maybe_id (np : NamePath) : Option Identifier :=
    match np {
        NamePath.npath ids => match ids {
            List.cons x rest => match rest {
                List.empty => Option.some x,
                _ => Option.none,
            },
            List.empty => Option.none,
        },
    }

/// Collect all names introduced by a declaration.
def names_of_decl (decl : Decl) : List Identifier :=
    match decl {
        Decl.def_d d =>
            match d {
                Def.mk {name, ..} =>
                    match np_to_maybe_id name {
                        Option.some id =>
                            let empty : List Identifier := List.empty in
                            List.cons id empty,
                        Option.none => List.empty,
                    },
            },
        Decl.inductive_d i =>
            match i {
                Inductive.mk name _ _ _ _ _ =>
                    match np_to_maybe_id name {
                        Option.some id =>
                            let empty : List Identifier := List.empty in
                            List.cons id empty,
                        Option.none => List.empty,
                    },
            },
        Decl.class_d c =>
            match c {
                Class.mk name _ _ _ _ =>
                    let empty : List Identifier := List.empty in
                    List.cons name empty,
            },
        Decl.struct_d s =>
            match s {
                Struct.mk name _ _ _ =>
                    let empty : List Identifier := List.empty in
                    List.cons name empty,
            },
        Decl.instance_d i =>
            match i {
                Instance.mk name _ _ _ _ _ _ =>
                    let empty : List Identifier := List.empty in
                    List.cons name empty,
            },
        // A scoped-open'd decl's own name is intentionally NOT collected
        // here yet (deliberate gap — full scoped-open semantics are out of
        // scope for now, see Decl.scoped_open_d's doc comment).
        _ => List.empty,
    }

/// Collect all names from a list of declarations.
///
/// One pass carrying a string-keyed seen-set. The previous fold called
/// `union_ids` per decl, whose `id_member` rescanned the entire
/// accumulated tail each time -- O(n^2) `String.beq` at the ~4000-def
/// whole-graph call (`names_of_decls dict_paramed2`, lang/module.mo),
/// which sat at 12.0s in the 2026-09-09 self-compile profile (AGENTS.md
/// item 27 diagnosed the shape at hello.mo scale and correctly deferred
/// it; item 37 is why it had to be re-measured at self-compile scale).
///
/// Output is unchanged from `union_ids`'s left bias: encounter order,
/// first occurrence kept. `id_eq` is exactly `String.beq` of the two
/// identifiers' strings, and `show_identifier` is exactly that string, so
/// keying the set on `show_identifier` dedups identically to `id_member`.
/// (`List.dedup_by`, std/list.mo, is no substitute: its own `seen` is a
/// plain list scanned linearly -- the same O(n^2).)
def names_of_decls (decl_list : List Decl) : List Identifier :=
    names_of_decls_go decl_list str_map_empty

// Mutually recursive through `keep_new_names`; each `keep_new_names`
// step consumes one name and each `names_of_decls_go` step one decl, so
// the pair always terminates -- the checker just can't see it across
// the mutual edge.
#[terminating]
def names_of_decls_go (decl_list : List Decl) (seen : HashMap String Identifier) : List Identifier :=
    match decl_list {
        List.cons hd rest => keep_new_names (names_of_decl hd) seen rest,
        List.empty => List.empty,
    }

/// Consume one decl's freshly collected names (`names_of_decl` returns 0
/// or 1 today, but this is written against the general list so a future
/// multi-name arm cannot silently drop names), then continue with the
/// rest of the decls and the updated seen-set.
#[terminating]
def keep_new_names (names : List Identifier) (seen : HashMap String Identifier) (rest : List Decl) : List Identifier :=
    match names {
        List.cons name more =>
            let key : String := show_identifier name in
            match str_map_lookup key seen {
                Option.some _ => keep_new_names more seen rest,
                Option.none =>
                    List.cons name (keep_new_names more (str_map_insert key name seen) rest),
            },
        List.empty => names_of_decls_go rest seen,
    }

/// Elaborate a single declaration.
def elaborate_decl (decl : Decl) (known_names : List Identifier) : Decl :=
    match decl {
        Decl.def_d d => Decl.def_d (elaborate_def d known_names),
        Decl.inductive_d i => Decl.inductive_d (elaborate_inductive i known_names),
        Decl.class_d c => Decl.class_d (elaborate_class c known_names),
        Decl.struct_d s => Decl.struct_d (elaborate_struct s known_names),
        Decl.instance_d i => Decl.instance_d (elaborate_instance i known_names),
        Decl.infix_d op p vis => Decl.infix_d op p vis,
        Decl.use_d p filter public => Decl.use_d p filter public,
        Decl.open_d p filter => Decl.open_d p filter,
        Decl.scoped_open_d p filter inner => Decl.scoped_open_d p filter (elaborate_decl inner known_names),
        // `def_macro_d`/`decl_gen_d`/`macro_call_d` (macro-expansion-
        // phase additions): passed through unchanged, same as
        // infix_d/use_d/open_d above — elaboration (forall-wrapping
        // free type vars) doesn't apply to an unexpanded macro
        // definition/invocation the same way it does to an ordinary
        // def/inductive; whatever a macro EXPANDS into gets elaborated
        // normally once it's a real decl. See `build_scope_one_decl`'s
        // own identical wildcard (lang/scope.mo) for why this can't be
        // left as a non-exhaustive match at all (no static
        // exhaustiveness check in this language — silently typechecks
        // fine, then crashes at runtime the moment a real decl of one
        // of these variants is matched).
        _ => decl,
    }

/// Elaborate all declarations in a module.
/// Builds known_names from the decl_list' own names plus existing names,
/// then maps elaborate_decl over each decl.
/// Mirrors Rust's elaborate_decls (type.rs:3074).
def elaborate_decls (decl_list : List Decl) (existing_names : List Identifier) : List Decl :=
    let decl_names := names_of_decls decl_list in
    let known_names := union_ids existing_names decl_names in
    elaborate_decls_map decl_list known_names

// Regression tests for `elaborate_decl`'s wildcard arm covering the 3
// macro-expansion-phase `Decl` variants (def_macro_d/decl_gen_d/
// macro_call_d) -- see `lang/scope.mo`'s own identical-purpose tests
// for `build_scope_one_decl` for the full rationale (no static
// exhaustiveness check in this language; a missing arm here would
// silently typecheck fine and only crash at RUNTIME). Each confirms
// `elaborate_decl` passes the value through unchanged (identity) --
// the fixture and the result are structurally the same decl shape.

def elaborate_test_macro_call_decl : Decl :=
    let name : Identifier := Identifier.id "foo" in
    let no_args : List Term := List.empty in
    Decl.macro_call_d name no_args

def elaborate_test_def_macro_decl : Decl :=
    let np : NamePath := NamePath.npath (List.cons (Identifier.id "foo") List.empty) in
    let no_constraints : List TypeConstraint := List.empty in
    let no_attrs : List Attribute := List.empty in
    Decl.def_macro_d (Def.mk np Term.hole Term.hole no_constraints no_attrs Visibility.package_private List.empty)

def elaborate_test_decl_gen_decl : Decl :=
    let np : NamePath := NamePath.npath (List.cons (Identifier.id "foo") List.empty) in
    let no_params : List Param := List.empty in
    let no_decls : List Decl := List.empty in
    let no_attrs : List Attribute := List.empty in
    Decl.decl_gen_d np no_params no_decls no_attrs

#[test]
def test_elaborate_decl_macro_call_d_passthrough : Bool :=
    let no_names : List Identifier := List.empty in
    match elaborate_decl elaborate_test_macro_call_decl no_names {
        Decl.macro_call_d name _ => id_eq name (Identifier.id "foo"),
        _ => false,
    }

#[test]
def test_elaborate_decl_def_macro_d_passthrough : Bool :=
    let no_names : List Identifier := List.empty in
    match elaborate_decl elaborate_test_def_macro_decl no_names {
        Decl.def_macro_d _ => true,
        _ => false,
    }

#[test]
def test_elaborate_decl_decl_gen_d_passthrough : Bool :=
    let no_names : List Identifier := List.empty in
    match elaborate_decl elaborate_test_decl_gen_decl no_names {
        Decl.decl_gen_d name _ _ _ => id_eq (Identifier.id "foo") (name_path_head name),
        _ => false,
    }

#[partial]
def name_path_head (np : NamePath) : Identifier :=
    match np { NamePath.npath ids => match ids { List.cons hd _ => hd } }

/// Map elaborate_decl over a list of decl_list with a fixed known_names set.
def elaborate_decls_map (decl_list : List Decl) (known_names : List Identifier) : List Decl :=
    match decl_list {
        List.cons hd rest =>
            let elaborated_hd := elaborate_decl hd known_names in
            let elaborated_rest := elaborate_decls_map rest known_names in
            List.cons elaborated_hd elaborated_rest,
        List.empty => List.empty,
    }

// ─── Level generalization (W1.3) ──────────────────────────────────────

/// A signature mentioning `Sort u` gains a binder for `u`.
///
/// This is a UNIT pin on `elaborate_type`, deliberately, because the
/// source-level pins in `lang/tests/typecheck_examples_tests.mo` cannot
/// see this yet: nothing consumes a level binder until W1.4 instantiates
/// them at call sites, so `def idL {A : Sort u} ...` checks the same
/// whether or not `u` is generalized. Measured, not assumed -- mutating
/// `elaborate_type` to generalize NOTHING leaves all 27 of those source
/// pins passing, and fails this one.
#[test]
def test_elaborate_type_binds_a_free_level_var : Bool :=
    let typ : Term := Term.sort (SortLevel.var (Identifier.id "u")) in
    match elaborate_type typ List.empty List.empty {
        Term.forall _dbg _kind _body => true,
        _ => false,
    }

/// ...and the binder is marked as a LEVEL binder, not a term binder.
/// `wrap_forall` marks a term binder `Term.type_ 1`; this one must be a
/// sort at level 0, which is what `is_level_binder_kind`
/// (`lang/typecheck/levels.mo`) reads to keep the two apart at the three
/// sites that open a `forall` chain.
#[test]
def test_level_binder_is_marked_as_a_sort : Bool :=
    let typ : Term := Term.sort (SortLevel.var (Identifier.id "u")) in
    match elaborate_type typ List.empty List.empty {
        Term.forall _dbg kind _body => match kind {
            Term.sort _l => true,
            _ => false,
        },
        _ => false,
    }

/// A type with NO level variable gains no level binder -- generalization
/// must not wrap every signature in the corpus.
#[test]
def test_concrete_type_gains_no_level_binder : Bool :=
    match elaborate_type (Term.type_ 1) List.empty List.empty {
        Term.forall _dbg _kind _body => false,
        _ => true,
    }

/// Level generalization is IDEMPOTENT. `registered_def_type`
/// (`lang/scope.mo`) runs `elaborate_def` over an already-elaborated
/// decl list, so `elaborate_type` meets its own output; `known_names`
/// keeps `wrap_forall` from re-wrapping the term variables, and
/// `bound_level_var_names` is that same guard for the level half.
/// Without it the chain grows one `forall u` per pass.
///
/// Asserted as "the second pass changes nothing", not as a binder count:
/// what matters is the fixpoint, and a count would have to be restated
/// whenever the marker or the ordering moved.
#[test]
def test_elaborate_type_level_generalization_is_idempotent : Bool :=
    let typ : Term := Term.sort (SortLevel.var (Identifier.id "u")) in
    let once : Term := elaborate_type typ List.empty List.empty in
    Similar.similar (elaborate_type once List.empty List.empty) once

/// The guard reads the binders' MARKER, not their position, so it still
/// finds a level binder sitting outside a term binder -- the shape
/// `elaborate_type` itself builds when a signature has both.
#[test]
def test_bound_level_var_names_finds_the_level_binder : Bool :=
    let inner : Term := Term.forall (DebugName.named (Identifier.id "A")) (Term.type_ 1) Term.hole in
    let t : Term := Term.forall (DebugName.named (Identifier.id "u"))
                                (Term.sort (SortLevel.concrete 0)) inner in
    match bound_level_var_names t {
        List.cons hd rest =>
            List.is_empty rest && Similar.similar hd (Identifier.id "u"),
        List.empty => false,
    }
