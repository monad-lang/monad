// Lower a `Term.elim` back to the `Literal.if_`/`Literal.match_` form that
// codegen and the evaluator still compile -- `core-term-simplification.md`
// R3c. The checker RETURNS `Term.elim` once R3c is wired; this is the one
// shared conversion, used by `codegen/emit.mo`'s whole-program decl pass
// and by `lang/lower_core_ir.mo` (eval / REPL / meta-eval).
//
// This is a representation change, not a semantic one. `Elim.minors` are
// POSITIONAL lambda chains in constructor-declaration order, binding one
// field per `Term.lam`; a `Literal.match_` case binds the same fields by
// name. The motive is dropped: it is a TYPING device, and iota on
// `Literal.match_` dispatches on the same scrutinee and fires the same minor.
//
// Strictness: the checker does not validate match-arm arity
// (`validate_cases_against_inductive` checks only the constructor name), so a
// minor with fewer lambdas than its constructor has fields is a real error
// (a de-Bruijn-misaligned arm) and is reported rather than realigned.

use lib::types {
  Binder, DebugName, Elim, Identifier, InductConstructor, Inductive, Literal, MatchCase,
  NamePath, Scope, Term, binder_name, list_reverse, show_name_path, term_peel,
}
use lib::scope {npath_eq, scope_find_inductive}
use std::list {List.length}

/// The `Literal` form of `e`, or a message naming the malformed minor.
/// `Bool`-shaped elims become `Literal.if_` (so the existing `if` codegen
/// path, whose `ensure_i1_cond` anchors to the constructor NAMED `true`, is
/// used unchanged); everything else becomes `Literal.match_`.
pub def elim_to_literal (scope : Scope) (e : Elim) : Result String Term :=
    match scope_find_inductive e.inductive scope {
        Result.err _ => Result.err (String.concat "unknown inductive " (show_name_path e.inductive)),
        Result.ok ind =>
            match elim_build_cases ind ind.constructors e.minors {
                Result.err msg => Result.err msg,
                Result.ok cases =>
                    match bool_shaped ind cases scope {
                        Option.some branch =>
                            match branch {
                                Pair.pair then_body else_body =>
                                    Result.ok (Term.lit (Literal.if_ e.scrutinee then_body else_body)),
                            },
                        Option.none => Result.ok (Term.lit (Literal.match_ e.scrutinee cases)),
                    },
            },
    }

/// `true`'s and `false`'s minor bodies, when `e` is an elim on `Bool` and both
/// constructors are present in `cases`. `Option.none` means "use `match_`".
def bool_shaped (ind : Inductive) (cases : List MatchCase) (scope : Scope) : Option (Pair Term Term) :=
    match scope_find_inductive (NamePath.mk (List.cons (Identifier.id "Bool") List.empty)) scope {
        Result.err _ => Option.none,
        Result.ok bool_ind =>
            if npath_eq bool_ind.name ind.name
            then
                match find_case_body "true" cases {
                    Option.none => Option.none,
                    Option.some then_body =>
                        match find_case_body "false" cases {
                            Option.none => Option.none,
                            Option.some else_body =>
                                let pair : Pair Term Term := Pair.pair then_body else_body in
                                Option.some pair,
                        },
                }
            else Option.none,
    }

/// The body of the case named `want`, by BARE constructor name.
#[partial]
def find_case_body (want : String) (cases : List MatchCase) : Option Term :=
    match cases {
        List.empty => Option.none,
        List.cons c rest =>
            match c {
                MatchCase.mk name _args body _fp _typ_name =>
                    match name {
                        Identifier.id s => if String.beq s want then Option.some body else find_case_body want rest,
                    },
            },
    }

/// One case per constructor, minors in the same (declaration) order.
def elim_build_cases (ind : Inductive) (ctors : List InductConstructor) (minors : List Term) : Result String (List MatchCase) :=
    match ctors {
        List.empty =>
            match minors {
                List.empty => Result.ok List.empty,
                List.cons _ _ => Result.err "Term.elim has more minors than its inductive has constructors",
            },
        List.cons ctor rest =>
            match minors {
                List.empty => Result.err "Term.elim is missing a minor for a constructor",
                List.cons minor mrest =>
                    match elim_case_for_ctor ind ctor minor {
                        Result.err msg => Result.err msg,
                        Result.ok case_ =>
                            match elim_build_cases ind rest mrest {
                                Result.err msg => Result.err msg,
                                Result.ok cases => Result.ok (List.cons case_ cases),
                            },
                    },
            },
    }

/// One constructor's minor as a `MatchCase`: peel exactly `ctor.params`'s
/// field count of lambdas (the body may itself be a lambda), name the binders
/// after the minor's own, and carry the inductive as `typ_name`.
def elim_case_for_ctor (ind : Inductive) (ctor : InductConstructor) (minor : Term) : Result String MatchCase :=
    match peel_minor_binders (List.length ctor.params) minor List.empty {
        Result.err msg => Result.err msg,
        Result.ok peeled =>
            match peeled {
                Pair.pair args body =>
                    let mc : MatchCase := MatchCase.mk (name_path_last_id ctor.name) args body Option.none (Option.some ind.name) in
                    Result.ok mc,
            },
    }

/// Peel `n` leading `Term.lam` binders off `t`, collecting one `Identifier`
/// per binder (outermost first), then return the args and the body under
/// them. The body is returned UNCHANGED: after exactly `n` binders it may be a
/// `Term.ctx`-wrapped arm body, and the pass must preserve source locations
/// ("every site that rebuilds preserves"). Only the leading-lambda DECISION
/// peels. `#[partial]`: the recursion is `I64`-bounded, the same idiom
/// `whnf_peel_lambda_n` uses.
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
/// `_`, the corpus's own spelling for one nobody reads (codegen binds it but
/// no body references it).
def binder_ident (b : Binder) : Identifier :=
    match binder_name b {
        DebugName.named id => id,
        DebugName.unnamed => Identifier.id "_",
    }

/// A constructor's bare name -- `NamePath`'s last segment. Mirrors
/// `infer.mo`'s `constructor_bare_name`, which `lang`'s dependency order
/// keeps out of reach here (`infer.mo` depends on this module's caller, not
/// the reverse).
#[partial]
def name_path_last_id (np : NamePath) : Identifier :=
    match np {
        NamePath.mk ids =>
            match List.last ids {
                Option.some last_id => last_id,
                Option.none => Identifier.id "",
            },
    }
