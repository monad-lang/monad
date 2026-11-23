// A `Term.elim`'s minors as per-constructor arms, for the two backends that
// compile it: `codegen/emit.mo` (LLVM) and `lang/lower_core_ir.mo` (eval /
// REPL / meta-eval). `core-term-simplification.md` R6, surface/core split S1.
//
// `Elim.minors` are POSITIONAL lambda chains in constructor-declaration order,
// binding one field per `Term.lam`. An arm is one minor with exactly its
// constructor's field count of lambdas peeled: the constructor, the binder
// names, and the body under them. The motive is a typing device and is not
// needed to run the elimination.
//
// Strictness: a minor with fewer lambdas than its constructor has fields is a
// de-Bruijn-misaligned arm and is reported rather than realigned.

use lib::types {Minor,
    Binder, DebugName, Elim, Identifier, InductConstructor, Inductive, NamePath, Scope, Term,
    binder_name, list_reverse, show_identifier, show_name_path, term_peel,
}
use lib::scope {scope_find_inductive}
use lib::name_text {string_matches_bare}
use std::list {}

/// One constructor's arm of an elimination.
pub struct ElimArm {
    /// The constructor's bare name (`cons`).
    ctor : Identifier,
    /// The inductive that owns it.
    owner : NamePath,
    /// One name per field, outermost first; `_` for an unnamed binder.
    binders : List Identifier,
    body : Term,
}

/// `e`'s inductive, resolved in `scope`, with its arms.
pub def elim_arms_in (scope : Scope) (e : Elim) : Result String (Pair Inductive (List ElimArm)) :=
    match scope_find_inductive e.inductive scope {
        Result.err _ => Result.err (String.concat "unknown inductive " (show_name_path e.inductive)),
        Result.ok ind =>
            match elim_arms ind e {
                Result.err msg => Result.err msg,
                Result.ok arms => Result.ok (Pair.pair ind arms),
            },
    }

/// One arm per constructor of `ind`, minors in the same (declaration) order.
pub def elim_arms (ind : Inductive) (e : Elim) : Result String (List ElimArm) :=
    arms_go ind ind.constructors e.minors

def arms_go (ind : Inductive) (ctors : List InductConstructor) (minors : List Minor) : Result String (List ElimArm) :=
    match ctors {
        List.empty =>
            match minors {
                List.empty => Result.ok List.empty,
                List.cons _ _ => Result.err "Term.elim has more minors than its inductive has constructors",
            },
        List.cons ctor rest =>
            match minors {
                List.empty => Result.err "Term.elim is missing a minor for a constructor",
                // An impossible constructor's tag never occurs, so it gets no arm.
                List.cons minor mrest =>
                    match minor {
                        Minor.impossible => arms_go ind rest mrest,
                        Minor.case body =>
                            match arm_for_ctor ind ctor body {
                                Result.err msg => Result.err msg,
                                Result.ok arm =>
                                    match arms_go ind rest mrest {
                                        Result.err msg => Result.err msg,
                                        Result.ok arms => Result.ok (List.cons arm arms),
                                    },
                            },
                    },
            },
    }

def arm_for_ctor (ind : Inductive) (ctor : InductConstructor) (minor : Term) : Result String ElimArm :=
    match peel_minor_binders (List.length ctor.params) minor List.empty {
        Result.err msg => Result.err msg,
        Result.ok peeled =>
            match peeled {
                Pair.pair binders body =>
                    let arm : ElimArm := { ctor := name_path_last_id ctor.name, owner := ind.name, binders := binders, body := body } in
                    Result.ok arm,
            },
    }

/// `true`'s and `false`'s arm bodies when `ind` is a two-constructor,
/// fieldless `Bool`, so a backend can compile the elimination as an `if`.
/// The branches are chosen by constructor NAME, not position. Names may be
/// module-qualified by then (`prelude::Bool`).
#[partial]
pub def bool_branches (ind : Inductive) (arms : List ElimArm) : Option (Pair Term Term) :=
    if Bool.not (string_matches_bare (show_name_path ind.name) "Bool")
        || Bool.not (I64.beq (List.length arms) 2)
    then Option.none
    else
        match nullary_arm_body arms "true" {
            Option.none => Option.none,
            Option.some then_body =>
                match nullary_arm_body arms "false" {
                    Option.none => Option.none,
                    Option.some else_body =>
                        let branches : Pair Term Term := Pair.pair then_body else_body in
                        Option.some branches,
                },
        }

#[partial]
def nullary_arm_body (arms : List ElimArm) (want : String) : Option Term :=
    match arms {
        List.empty => Option.none,
        List.cons a rest => if arm_is_nullary a want then Option.some a.body else nullary_arm_body rest want,
    }

def arm_is_nullary (a : ElimArm) (want : String) : Bool :=
    string_matches_bare (show_identifier a.ctor) want && I64.beq (List.length a.binders) 0

/// Peel `n` leading `Term.lam` binders off `t`, collecting one `Identifier`
/// per binder (outermost first), then return the binders and the body under
/// them. The body is returned UNCHANGED: after exactly `n` binders it may be a
/// `Term.ctx`-wrapped arm body, and source locations must survive. Only the
/// leading-lambda DECISION peels.
#[partial]
def peel_minor_binders (n : I64) (t : Term) (acc : List Identifier) : Result String (Pair (List Identifier) Term) :=
    if I64.lt n 1
    then
        let out : Pair (List Identifier) Term := Pair.pair (list_reverse acc) t in
        Result.ok out
    else
        match term_peel t {
            Term.lam b _typ body => peel_minor_binders (n - 1) body (List.cons (binder_ident b) acc),
            _ => Result.err "Term.elim minor has fewer lambdas than its constructor has fields",
        }

/// The identifier a minor's binder stands for. An unnamed binder reports as
/// `_`, the corpus's own spelling for one nobody reads.
def binder_ident (b : Binder) : Identifier :=
    match binder_name b {
        DebugName.named id => id,
        DebugName.unnamed => Identifier.id "_",
    }

/// A constructor's bare name -- `NamePath`'s last segment.
#[partial]
def name_path_last_id (np : NamePath) : Identifier :=
    match np {
        NamePath.mk ids =>
            match List.last ids {
                Option.some last_id => last_id,
                Option.none => Identifier.id "",
            },
    }
