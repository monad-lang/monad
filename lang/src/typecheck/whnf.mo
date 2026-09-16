use lib::types {DebugName, LocalScope, Scope, Term, sentinel, term_peel}
use lib::scope {scope_find_def_body, scope_find_local, scope_resolve_name}
use lib::typecheck::subst {beta_reduce}

// ─── Weak-head normal form ───────────────────────────────────────────
//
// Conversion checking: two types are definitionally equal when they
// REDUCE to the same thing, not only when they are written the same
// way. `lang/typecheck/unify.mo` compares `Term`s structurally, so a
// declared type that is still an unreduced application (`identity_type
// foo`) never gets compared against what it computes to (`Bool`). This
// module supplies the missing reduction step; `unify` calls it only
// after a structural comparison has already failed, so the happy path
// pays nothing.
//
// Two reduction rules, which is what conversion checking at this stage
// needs:
//
//   beta   `(fn x => body) arg`  ->  `body[x := arg]`
//   delta  a free `Term.var` naming a global def  ->  that def's body
//
// Both are needed together, and neither is useful alone here: a
// type-level application like `identity_type foo` is headed by a FREE
// variable, not a `Term.lam`, so beta has nothing to fire on until
// delta has unfolded the head into the `Term.lam` chain a `def`'s body
// actually is (`def_params_of_term`, `lang/scope.mo`).
//
// NOT implemented, deliberately: iota (reducing a `match`/`if` whose
// scrutinee is a known constructor). Nothing in conversion checking
// needs it yet, and `Literal.match_`'s arms are a binding form that
// binds `List.length args` de Bruijn levels at once (AGENTS.md item
// 22) -- the place where this kind of code goes subtly wrong. It is the
// natural next increment.
//
// There is no metavariable handling here because this checker has no
// metavariables: `Term.hole` is a matches-anything wildcard, not a
// solvable meta (see `unify`'s own `Term.hole` arms). A reducer for a
// checker WITH metas would have to avoid committing to a reduction
// path before they are solved.

/// Default step budget. Conversion checking needs a handful of steps --
/// unfold a type-level def, beta it, look at the head -- so this is
/// generous rather than tight. It is a bound on DIVERGENCE, not a
/// tuning knob: the self-hosted compiler has no termination checker
/// yet, and `#[partial]` is applied to ~2000 defs in this tree, so
/// nothing verifies that an unfolded body terminates. Running out of
/// fuel is not an error -- reduction simply stops and the term is
/// compared in whatever form it reached, which is exactly the
/// (conservative) behaviour this had before reduction existed.
def whnf_fuel : I64 := 64

/// Reduce `t` to weak-head normal form: keep reducing at the HEAD until
/// the head is rigid (a `pi`, a sort, a literal, a constructor, a
/// variable with no body, ...). Sub-terms are left alone -- the head is
/// all a structural comparison looks at before recursing, and each
/// recursive step goes back through `unify`, which reduces again.
def whnf (scope : Scope) (locals : LocalScope) (t : Term) : Term :=
    whnf_go whnf_fuel scope locals t

/// `#[partial]`: fuel-bounded, but the decrement is not a structural
/// subterm the checker can see.
#[partial]
def whnf_go (fuel : I64) (scope : Scope) (locals : LocalScope) (t0 : Term) : Term :=
    // Peel `Term.ctx` here rather than at each arm: a located wrapper
    // would otherwise fall through to the rigid-head case and stop
    // reduction dead, silently.
    let t : Term := term_peel t0 in
    if I64.lt fuel 1 then
        t
    else
        match t {
            Term.app f a =>
                // Reducing `f` recursively is what handles a spine of
                // any length: `f g x` reduces `f g` first, so a
                // multi-parameter def unfolds and betas one argument at
                // a time without collecting the spine explicitly.
                let f_r : Term := whnf_go (fuel - 1) scope locals f in
                match f_r {
                    Term.lam _dbg _typ body => whnf_go (fuel - 1) scope locals (beta_reduce body a),
                    // Stuck head. Keep the reduced head anyway -- it is
                    // no less reduced than what came in, and a caller
                    // comparing two stuck applications compares heads.
                    _ => Term.app f_r a,
                },
            Term.var idx dbg =>
                if I64.beq idx sentinel then
                    match whnf_delta scope locals dbg {
                        Option.some body => whnf_go (fuel - 1) scope locals body,
                        Option.none => t,
                    }
                else
                    // A bound de Bruijn variable. Its binder is outside
                    // this term, so there is nothing to unfold.
                    t,
            // Rigid heads: `pi`, `forall`, `type_`, `lit`, `ntv`, `con`,
            // `hole`, and the two macro-only forms. Already in WHNF.
            _ => t,
        }

/// Delta: the body of the global `def` this free variable names, if it
/// names one.
///
/// The local check is not an optimisation -- it is what keeps this
/// sound. A free `Term.var` is not necessarily a global: `locals_with_
/// def_typevars` (`lang/module.mo`) skolemises a def's implicit type
/// parameters into NAMED locals, and those resolve through this same
/// path. Unfolding a local `V` into a same-named global `V`'s body
/// would substitute an unrelated definition for a bound type variable.
def whnf_delta (scope : Scope) (locals : LocalScope) (dbg : DebugName) : Option Term :=
    match dbg {
        DebugName.named id =>
            match scope_find_local id locals {
                Option.some _ => Option.none,
                Option.none =>
                    // Resolve first, then look the body up under the
                    // name resolution returned: the same two-step
                    // `type_check_free_var` uses for `def_sigs`, so a
                    // bare name and its qualified form reach the same
                    // entry.
                    match scope_resolve_name (NameRef.nid id) scope locals {
                        ok sd => scope_find_def_body sd.name scope,
                        err _ => Option.none,
                    },
            },
        DebugName.unnamed => Option.none,
    }
