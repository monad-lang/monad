// An instance method's written signature against its class's (ISSUE-14).
//
// `promote_methods` (`lang/src/scope.mo`) copies each method's own `typ`
// into the promoted def, which is then checked against that same `typ`, so
// a signature that disagrees with the class was never noticed. This module
// compares the two. It reports and rewrites nothing: the decls codegen
// sees are unchanged.
use lib::types {
    Class, ClassDef, DebugName, Def, Identifier, Instance, LocalScope, NameRef, NamePath, Scope,
    Term, TypeError, id_eq, sentinel, show_name_path, union_ids,
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
/// instance's argument in the same position, and every instance-determined
/// variable (`{S : Type}`) by its solution.
def expected_method_type (cls : Class) (ins : Instance) (solution : List (Pair Identifier Term)) (cd : ClassDef)
    : Term :=
    apply_solution solution (subst_class_params cls ins.args cd.typ)

#[partial]
def apply_solution (solution : List (Pair Identifier Term)) (t : Term) : Term :=
    match solution {
        List.empty => t,
        List.cons p rest =>
            match p {
                Pair.pair x v => apply_solution rest (name_subst_term x v t),
            },
    }

// --- Instance-determined variables -------------------------------------------
//
// `class MonadState {S : Type} (M : Type -> Type)`: each instance fixes S once.
// It is solved by matching every annotated method's class signature against
// the written one; the first binding wins, so a method that disagrees then
// fails the ordinary comparison below.

def determined_names (cls : Class) : List Identifier := param_names cls.determined

/// The binding for each determined variable that some annotated method fixes.
def determined_solution (cls : Class) (ins : Instance) (ivars : List Identifier) (scope : Scope)
    (locals : LocalScope) : List (Pair Identifier Term) :=
    solve_defs cls ins ivars (determined_names cls) ins.defs scope locals List.empty

#[partial]
def solve_defs (cls : Class) (ins : Instance) (ivars : List Identifier) (dvars : List Identifier) (defs : List Def)
    (scope : Scope) (locals : LocalScope) (acc : List (Pair Identifier Term)) : List (Pair Identifier Term) :=
    match defs {
        List.empty => acc,
        List.cons d rest =>
            let next : List (Pair Identifier Term) :=
                match class_method_for cls.methods d {
                    Option.none => acc,
                    Option.some cd =>
                        if is_whole_hole d.typ then acc
                        else
                            let pattern : Term := subst_class_params cls ins.args cd.typ in
                            let wl : List Identifier := method_local_vars d.typ ivars scope locals in
                            let el : List Identifier :=
                                method_local_vars pattern (union_ids dvars ivars) scope locals in
                            let written : Term := align_typevars wl el d.typ in
                            match_determined dvars (union_ids wl el) (canonicalize_bound_var_names pattern)
                                (canonicalize_bound_var_names written) acc,
                } in
            solve_defs cls ins ivars dvars rest scope locals next,
    }

/// One-way match: a determined variable in `pattern` binds the `target`
/// subterm at the same position, unless already bound. Shapes that differ
/// bind nothing; the comparison after substitution reports them. A target
/// mentioning one of the method's own type variables (`forbidden`) is not a
/// binding: `put (s : A)` is polymorphic in S, it does not fix it.
#[terminating]
def match_determined (dvars : List Identifier) (forbidden : List Identifier) (pattern : Term) (target : Term)
    (acc : List (Pair Identifier Term)) : List (Pair Identifier Term) :=
    match determined_var dvars pattern {
        Option.some x =>
            if is_bound x acc || mentions_bound_var target || any_in (free_vars target List.empty) forbidden
            then acc
            else List.cons (Pair.pair x target) acc,
        Option.none =>
            match pattern {
                Term.ctx _ p => match_determined dvars forbidden p target acc,
                Term.app pf pa =>
                    match peel_ctx target {
                        Term.app tf ta =>
                            match_determined dvars forbidden pa ta (match_determined dvars forbidden pf tf acc),
                        _ => acc,
                    },
                Term.pi _ pd pr =>
                    match peel_ctx target {
                        Term.pi _ td tr =>
                            match_determined dvars forbidden pr tr (match_determined dvars forbidden pd td acc),
                        _ => acc,
                    },
                _ => acc,
            },
    }

#[partial]
def peel_ctx (t : Term) : Term :=
    match t {
        Term.ctx _ inner => peel_ctx inner,
        _ => t,
    }

def determined_var (dvars : List Identifier) (t : Term) : Option Identifier :=
    match peel_ctx t {
        Term.var idx dbg =>
            match dbg {
                DebugName.named id => if I64.beq idx sentinel && id_in id dvars then Option.some id else Option.none,
                DebugName.unnamed => Option.none,
            },
        _ => Option.none,
    }

#[partial]
def id_in (id : Identifier) (ids : List Identifier) : Bool :=
    match ids {
        List.empty => false,
        List.cons x rest => id_eq id x || id_in id rest,
    }

#[partial]
def any_in (ids : List Identifier) (set : List Identifier) : Bool :=
    match ids {
        List.empty => false,
        List.cons x rest => id_in x set || any_in rest set,
    }

#[partial]
def is_bound (x : Identifier) (acc : List (Pair Identifier Term)) : Bool :=
    match acc {
        List.empty => false,
        List.cons p rest =>
            match p {
                Pair.pair y _ => id_eq x y || is_bound x rest,
            },
    }

/// A solution is lifted out of its position, so it may not mention a variable
/// bound there. Shapes this walk does not know count as mentioning one.
#[partial]
def mentions_bound_var (t : Term) : Bool :=
    match t {
        Term.var idx _ => Bool.not (I64.beq idx sentinel),
        Term.ctx _ inner => mentions_bound_var inner,
        Term.app f a => mentions_bound_var f || mentions_bound_var a,
        Term.lit _ => false,
        Term.con _ => false,
        Term.sort _ => false,
        _ => true,
    }

/// The determined variables no annotated method fixes.
#[partial]
def unsolved (dvars : List Identifier) (solution : List (Pair Identifier Term)) : List Identifier :=
    match dvars {
        List.empty => List.empty,
        List.cons x rest =>
            if is_bound x solution then unsolved rest solution else List.cons x (unsolved rest solution),
    }

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
    let solution : List (Pair Identifier Term) := determined_solution cls ins ivars scope locals in
    list_concat (unsolved_errors ins (unsolved (determined_names cls) solution))
        (method_errors cls ins ivars solution ins.defs scope locals)

#[partial]
def unsolved_errors (ins : Instance) (xs : List Identifier) : List (Pair Identifier TypeError) :=
    match xs {
        List.empty => List.empty,
        List.cons x rest =>
            List.cons (Pair.pair x (TypeError.instance_determined_unsolved ins.cls x)) (unsolved_errors ins rest),
    }

#[partial]
def list_concat (a : List (Pair Identifier TypeError)) (b : List (Pair Identifier TypeError))
    : List (Pair Identifier TypeError) :=
    match a {
        List.empty => b,
        List.cons x rest => List.cons x (list_concat rest b),
    }

#[partial]
def method_errors (cls : Class) (ins : Instance) (ivars : List Identifier) (solution : List (Pair Identifier Term))
    (defs : List Def) (scope : Scope) (locals : LocalScope) : List (Pair Identifier TypeError) :=
    match defs {
        List.empty => List.empty,
        List.cons d rest =>
            let tail := method_errors cls ins ivars solution rest scope locals in
            match method_error cls ins ivars solution d scope locals {
                Option.none => tail,
                Option.some e => List.cons e tail,
            },
    }

def method_error (cls : Class) (ins : Instance) (ivars : List Identifier) (solution : List (Pair Identifier Term))
    (d : Def) (scope : Scope) (locals : LocalScope) : Option (Pair Identifier TypeError) :=
    let mname : Identifier := def_bare_name d in
    match class_method_for cls.methods d {
        Option.none =>
            Option.some (Pair.pair mname (TypeError.instance_method_not_in_class ins.cls mname)),
        Option.some cd =>
            if is_whole_hole d.typ then Option.none
            else
                let expected : Term := expected_method_type cls ins solution cd in
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

/// An unannotated method (`def df := 5`) has nothing written to compare;
/// its body is checked against the class signature instead
/// (`unannotated_methods`).
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

/// Each unannotated method that names a class method, with the class's
/// type for it at this instance: the type its body must check against.
/// The parser's untyped fallback discards an unannotated method's
/// parameters (`def nm (a : Bool) := "x"` is the constant `"x"`), so the
/// body alone is what an instance supplies.
pub def unannotated_methods (cls : Class) (ins : Instance) (scope : Scope) (locals : LocalScope)
    : List (Pair Def Term) :=
    unannotated_go cls ins (determined_solution cls ins (instance_vars ins) scope locals) ins.defs

#[partial]
def unannotated_go (cls : Class) (ins : Instance) (solution : List (Pair Identifier Term)) (defs : List Def)
    : List (Pair Def Term) :=
    match defs {
        List.empty => List.empty,
        List.cons d rest =>
            let tail := unannotated_go cls ins solution rest in
            if Bool.not (is_whole_hole d.typ) then tail
            else
                match class_method_for cls.methods d {
                    Option.none => tail,
                    Option.some cd => List.cons (Pair.pair d (expected_method_type cls ins solution cd)) tail,
                },
    }
