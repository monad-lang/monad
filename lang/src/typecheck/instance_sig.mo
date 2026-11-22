// An instance method's written signature against its class's (ISSUE-14).
//
// `promote_methods` (`lang/src/scope.mo`) copies each method's own `typ`
// into the promoted def, which is then checked against that same `typ`, so
// a signature that disagrees with the class was never noticed. This module
// compares the two. It reports and rewrites nothing: the decls codegen
// sees are unchanged.
use lib::types {
    Class, ClassDef, DebugName, Def, Identifier, Instance, LocalScope, NameRef, NamePath, Scope,
    Term, TypeError, show_name_path, union_ids,
}
use lib::scope {
    instance_method_name_matches, instance_wildcard_names, param_names,
    scope_resolve_name, subst_class_params,
}
use lib::elaborate {free_vars}
use lib::typecheck::name_subst {name_subst_term}
use lib::typecheck::unify {unify}
use lib::typecheck::infer {canonicalize_bound_var_names}

/// The class's declared type for `cd`, at this instance: every class
/// parameter (type or term, e.g. `LawfulMonad`'s `bind`) replaced by the
/// instance's argument in the same position.
def expected_method_type (cls : Class) (ins : Instance) (cd : ClassDef) : Term :=
    subst_class_params cls ins.args cd.typ

/// The class method `d` implements, by bare name.
#[partial]
def class_method_for (methods : List ClassDef) (d : Def) : Option ClassDef :=
    match methods {
        List.empty => Option.none,
        List.cons cd rest =>
            if instance_method_name_matches d.name cd.name
            then Option.some cd
            else class_method_for rest d,
    }

/// The method's own type variables, in first-occurrence order: free names
/// that resolve to nothing in scope and are not the instance's own
/// variables (`E` in `Functor (Result E)` stays rigid on both sides).
def method_local_vars (t : Term) (instance_vars : List Identifier) (scope : Scope)
    (locals : LocalScope) : List Identifier :=
    unresolved (free_vars t instance_vars) scope locals

#[partial]
def unresolved (ids : List Identifier) (scope : Scope) (locals : LocalScope) : List Identifier :=
    match ids {
        List.empty => List.empty,
        List.cons id rest =>
            match scope_resolve_name (NameRef.nid id) scope locals {
                Result.ok _ => unresolved rest scope locals,
                Result.err _ => List.cons id (unresolved rest scope locals),
            },
    }

def instance_vars (ins : Instance) : List Identifier :=
    union_ids (instance_wildcard_names ins)
        (union_ids (param_names ins.implicit_params) (args_free_vars ins.args))

#[partial]
def args_free_vars (args : List Term) : List Identifier :=
    match args {
        List.empty => List.empty,
        List.cons a rest => union_ids (free_vars a List.empty) (args_free_vars rest),
    }

/// The written signature with its method-local variables renamed to the
/// class's, position by position (`map (f : X -> Y)` against
/// `map (f : A -> B)`). Two passes through placeholders keep the renaming
/// simultaneous. Different counts leave it alone, so the comparison below
/// fails rather than guessing.
def align_typevars (from_ids : List Identifier) (to_ids : List Identifier) (t : Term) : Term :=
    if Bool.not (I64.beq (List.length from_ids) (List.length to_ids)) then t
    else rename_to to_ids (List.length from_ids) (rename_to_placeholders from_ids 0 t)

def placeholder (i : I64) : Identifier :=
    Identifier.id (String.concat "__instance_sig_tv_" (I64.to_string i))

#[partial]
def rename_to_placeholders (ids : List Identifier) (i : I64) (t : Term) : Term :=
    match ids {
        List.empty => t,
        List.cons id rest =>
            rename_to_placeholders rest (i + 1) (name_subst_term id (named_var (placeholder i)) t),
    }

def rename_to (ids : List Identifier) (n : I64) (t : Term) : Term :=
    rename_to_go ids 0 n t

#[partial]
def rename_to_go (ids : List Identifier) (i : I64) (n : I64) (t : Term) : Term :=
    match ids {
        List.empty => t,
        List.cons id rest =>
            if I64.lt i n
            then rename_to_go rest (i + 1) n (name_subst_term (placeholder i) (named_var id) t)
            else t,
    }

def named_var (id : Identifier) : Term :=
    Term.var (0 - 1) (DebugName.named id)

/// Every way `ins`'s written methods disagree with `cls`.
pub def instance_signature_errors (cls : Class) (ins : Instance) (scope : Scope)
    (locals : LocalScope) : List (Pair Identifier TypeError) :=
    let ivars : List Identifier := instance_vars ins in
    method_errors cls ins ivars ins.defs scope locals

#[partial]
def method_errors (cls : Class) (ins : Instance) (ivars : List Identifier) (defs : List Def)
    (scope : Scope) (locals : LocalScope) : List (Pair Identifier TypeError) :=
    match defs {
        List.empty => List.empty,
        List.cons d rest =>
            let tail := method_errors cls ins ivars rest scope locals in
            match method_error cls ins ivars d scope locals {
                Option.none => tail,
                Option.some e => List.cons e tail,
            },
    }

def method_error (cls : Class) (ins : Instance) (ivars : List Identifier) (d : Def)
    (scope : Scope) (locals : LocalScope) : Option (Pair Identifier TypeError) :=
    let mname : Identifier := def_bare_name d in
    match class_method_for cls.methods d {
        Option.none =>
            Option.some (Pair.pair mname (TypeError.instance_method_not_in_class ins.cls mname)),
        Option.some cd =>
            if is_whole_hole d.typ then Option.none
            else
                let expected : Term := expected_method_type cls ins cd in
                let written : Term :=
                    align_typevars (method_local_vars d.typ ivars scope locals)
                        (method_local_vars expected ivars scope locals) d.typ in
                let e : Term := canonicalize_bound_var_names expected in
                let w : Term := canonicalize_bound_var_names written in
                match unify e w scope locals {
                    Result.ok _ => Option.none,
                    Result.err _ =>
                        Option.some (Pair.pair mname
                            (TypeError.instance_method_signature ins.cls mname expected d.typ)),
                },
    }

/// An unannotated method (`def show a := ...`) has nothing written to
/// compare; its body is checked against the class signature separately.
#[partial]
def is_whole_hole (t : Term) : Bool :=
    match t {
        Term.hole => true,
        Term.ctx _ inner => is_whole_hole inner,
        _ => false,
    }

def def_bare_name (d : Def) : Identifier :=
    match d.name {
        NamePath.mk ids =>
            match ids {
                List.cons only rest =>
                    match rest {
                        List.empty => only,
                        List.cons _ _ => Identifier.id (show_name_path d.name),
                    },
                List.empty => Identifier.id (show_name_path d.name),
            },
    }
