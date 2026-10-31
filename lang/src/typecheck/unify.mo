use lib::types {
  LocalScope, Scope, Similar, SortLevel, Term, TypeError, binder_is_explicit,
  level_le, sentinel, sort_level_of, term_peel
}
use lib::typecheck::whnf {whnf}

/// Structural type unification. Returns the unified type.
/// Holes match anything. Pi matches Pi structurally.
/// App spines are congruent: heads and arguments compare separately.
/// Lambdas compare the binder's own type, then the bodies.
/// Sorts respect cumulativity (level ≤ expected_level).
/// A non-explicit binder -- a quantified type variable or a universe level,
/// which `Term.forall` used to spell -- is stripped before comparison, on
/// either side.
/// Peels both sides at entry rather than adding a `Term.ctx` arm to each
/// of the four matches below. Every one of them tests SHAPE with a `_ =>`
/// fallback, so a wrapper would not crash -- a wrapped `Term.pi` would just
/// fall through to `Similar.similar` and report a spurious mismatch, which
/// is the silent kind of wrong.
///
/// Placement rule R1 says a wrapper never reaches a type position and so
/// never reaches here at all. This peels anyway: the recursive calls below
/// go through `unify`, so one peel at the top covers every level.
///
/// CONVERSION CHECKING. `scope`/`locals` are here for definitional
/// equality: when the structural comparison fails, both sides are
/// reduced to weak-head normal form (`lang/typecheck/whnf.mo`) and
/// compared once more, so a type still written as an unreduced
/// application (`identity_type foo`) is compared against what it
/// computes to (`Bool`) instead of being rejected on its spelling.
///
/// Reduction happens ONLY on the failing path, never at entry. Three
/// reasons, in order of how much they matter:
///   1. Cost. `unify` is hot; this way the succeeding comparison -- the
///      overwhelming majority -- does no extra work at all.
///   2. It can only ever ACCEPT more. Reduction is reached exactly
///      where an error was about to be returned, so no program that
///      type-checked before can start failing.
///   3. It bounds the recursion. One retry, on already-reduced
///      operands, cannot re-enter reduction.
///
/// `#[terminating]`: `term_peel` strictly removes wrappers, so the pair it
/// hands `unify_go` is smaller, but that is not a structural subterm the
/// checker can see.
#[terminating]
def unify (a : Term) (b : Term) (scope : Scope) (locals : LocalScope) : Result TypeError Term :=
    unify_go (term_peel a) (term_peel b) scope locals true

/// `unify` without conversion checking -- the exact behaviour this
/// module had before reduction existed.
///
/// For callers that treat a failed unification as ordinary control flow
/// rather than as an error. `try_type_check_def_call`
/// (`lang/typecheck/infer.mo`) is the one such caller: it unifies a
/// call's return type against the expected type and falls back to the
/// substituted return type when that fails. Reduction there cannot
/// change the outcome -- the only comparisons it newly accepts are the
/// ones `unify_stuck` resolves, and those return the expected type
/// UNREDUCED, which is the same term the caller already falls back to.
/// Since that path runs for essentially every call in the corpus,
/// paying for a reduction whose result is discarded either way is the
/// one place where this feature would cost real time for nothing.
#[terminating]
def unify_structural (a : Term) (b : Term) (scope : Scope) (locals : LocalScope) : Result TypeError Term :=
    unify_go (term_peel a) (term_peel b) scope locals false

/// `reduce` is the retry budget: `true` on the way in, `false` once
/// both sides have been reduced, so a reduced pair cannot ask to be
/// reduced again. It is a parameter rather than two copies of this
/// function so that every `mismatch` leaf below gets the retry without
/// each one having to remember to ask for it.
///
/// Note the budget is per-LEVEL, not global: the recursive calls below
/// go back through `unify`, which starts a fresh one. That is what lets
/// `Pi (idt A) B` convert against `Pi A B`. Each individual reduction
/// is fuel-bounded and only ever fires on a comparison that was already
/// failing, so this terminates in practice -- but it is bounded by
/// those two facts, not by construction.
#[partial]
def unify_go (a : Term) (b : Term) (scope : Scope) (locals : LocalScope) (reduce : Bool) : Result TypeError Term :=
    match a {
        Term.hole => ok b,
        // All three binder flavours arrive here now, and the two old
        // `Term.forall` arms fold into the two guards. A NON-EXPLICIT
        // binder on `a` is transparent exactly as `forall` was: strip it
        // and retry. It binds a quantified type variable or a universe
        // level rather than an argument the two sides could be compared
        // on, and its domain is a bare sort, so the structural comparison
        // below is not the same question.
        Term.pi b1 arg1 ret1 =>
            if Bool.not (binder_is_explicit b1)
            then unify ret1 b scope locals
            else
                match b {
                    Term.hole => ok a,
                    Term.pi b2 arg2 ret2 =>
                        if binder_is_explicit b2
                        then
                            match unify arg1 arg2 scope locals {
                                ok _ => unify ret1 ret2 scope locals,
                                err e => err e,
                            }
                        else unify a ret2 scope locals,
                    _ => unify_stuck a b scope locals reduce,
                },
        // A lambda against a lambda: the binder's own type, then the bodies.
        // Both bodies sit one binder deep under their OWN binder and `unify`
        // compares de Bruijn indices structurally, so no shift is involved;
        // binder names are annotations and take no part. Eta is deliberately
        // absent -- `fn x => f x` against a bare `f` needs the domain to type
        // the binder from -- and `test_unify_lam_is_not_eta` pins that gap.
        Term.lam _b1 typ1 body1 => match b {
            Term.hole => ok a,
            Term.lam _b2 typ2 body2 =>
                if Similar.similar a b then
                    ok a
                else
                    match unify typ1 typ2 scope locals {
                        ok _ => unify body1 body2 scope locals,
                        err _ => unify_stuck a b scope locals reduce,
                    },
            // A lambda is never similar to a pi, so the catch-all's
            // transparent-quantifier rule reduces to its strip here.
            Term.pi b2 _dom body2 =>
                if binder_is_explicit b2
                then unify_stuck a b scope locals reduce
                else unify a body2 scope locals,
            _ => unify_stuck a b scope locals reduce,
        },
        Term.sort l1 => unify_sort a l1 b scope locals reduce,
        // P2 (plans/type-system/core-term-simplification.md): spine
        // congruence. `unify_stuck`'s whole-spine reduction is weak-head
        // -- it stops at a stuck head and never looks inside an
        // argument -- so `A (idt P)` vs `A P` used to fail on spelling
        // while `idt P` vs `P` alone succeeds, and an argument hole
        // (`A hole` vs `A P`) failed the same way. This is load-bearing
        // for Stage 2, where every boundary comparison has the shape
        // `A i` with `A` a stuck line and `i` a dimension.
        //
        // `Similar.similar` first, as the fast path it already was:
        // syntactic identity of the whole spine answers without
        // walking it arm by arm. Then heads, then arguments, each
        // through `unify` so a component gets its own conversion
        // budget -- the same per-level-budget arrangement the Pi arm
        // above recurses under. A component failure falls back to
        // `unify_stuck` on the WHOLE spine, so nothing the catch-all
        // accepted stops being accepted: the arm only ever accepts
        // more, by congruence -- two spines are convertible when their
        // heads are and their arguments are.
        Term.app f1 x1 => match b {
            Term.hole => ok a,
            // The stripped-`forall` case, now a guard: a non-explicit
            // binder on `b` is transparent on this side too.
            Term.pi b2 _dom body2 =>
                if binder_is_explicit b2
                then unify_stuck a b scope locals reduce
                else unify a body2 scope locals,
            Term.app f2 x2 =>
                if Similar.similar a b then
                    ok a
                else
                    match unify f1 f2 scope locals {
                        ok _ =>
                            match unify x1 x2 scope locals {
                                ok _ => ok a,
                                err _ => unify_stuck a b scope locals reduce,
                            },
                        err _ => unify_stuck a b scope locals reduce,
                    },
            _ => unify_stuck a b scope locals reduce,
        },
        _ => match b {
            Term.hole => ok a,
            // ...and on the catch-all side.
            Term.pi b2 _dom body2 =>
                if binder_is_explicit b2
                then
                    if Similar.similar a b then
                        ok a
                    else
                        unify_stuck a b scope locals reduce
                else unify a body2 scope locals,
            _ =>
                if Similar.similar a b then
                    ok a
                else
                    unify_stuck a b scope locals reduce,
        },
    }

/// The sort arm.
///
/// Cumulativity: `Sort l1 <= Sort l2` holds exactly when `l1 <= l2`, and the
/// comparison is DIRECTIONAL — `a` is the actual, `b` the expected, so
/// `Type` checked against `Prop` must fail while `Prop` against `Type`
/// succeeds. `unify` is the only place subsumption belongs; a call site
/// instantiating a level is solving, not subsuming.
///
/// `b` is read through `sort_level_of` rather than shape-matched, so the
/// comparison runs on LEVELS and folds `level_const` (`level_le`) instead
/// of requiring a particular level shape. That is what lets a level the
/// checker computed -- `type_check_sort_full`'s `succ`, `type_check_pi`'s
/// `max` -- meet a numeral level without the comparison turning into a
/// mismatch, and what keeps a `Prop`/`Type`/`Sort n` written in source
/// comparable with the same sort built by the checker.
/// `#[terminating]`: this def rejoins the `unify_go`/`unify_stuck` cycle
/// through `unify_stuck`'s reduce-once path, and that bound is the cluster's
/// existing one -- `unify_stuck` clears the `reduce` flag before it recurses,
/// so a second failure in the nested pass reports the mismatch instead of
/// reducing again. It is the same argument that makes `unify` itself carry
/// the attribute (see its note above); it is a bound we can argue, not a
/// structural subterm the checker can see.
#[terminating]
def unify_sort (a : Term) (l1 : SortLevel) (b : Term) (scope : Scope) (locals : LocalScope) (reduce : Bool) : Result TypeError Term :=
    match b {
        Term.hole => ok a,
        _ => match sort_level_of b {
            Option.some l2 =>
                if level_le l1 l2 then
                    ok a
                else
                    err (TypeError.mismatch a b),
            Option.none => unify_stuck a b scope locals reduce,
        },
    }

/// The structural comparison failed. If either side can reduce, reduce
/// both and compare once more; otherwise report the mismatch.
///
/// On success this returns `a` -- the ORIGINAL, unreduced expected type,
/// not the reduced one. `unify`'s result is what the caller records as
/// the term's type (`mk_typed`, `lang/typecheck/infer.mo`), so handing
/// back a reduced type would change what later inference sees, well
/// beyond making this comparison succeed. The reduced forms are used to
/// DECIDE, never to replace.
///
/// The mismatch is reported against the original terms too, for the
/// same reason in reverse: an error naming a term the user never wrote
/// is worse than one naming the term they did.
def unify_stuck (a : Term) (b : Term) (scope : Scope) (locals : LocalScope) (reduce : Bool) : Result TypeError Term :=
    // The O(1) guard matters. This path is not rare: `try_type_check_
    // def_call` (`lang/typecheck/infer.mo`) unifies a call's return
    // type against the expected type and treats failure as ordinary
    // control flow, so a failing `unify` is a routine event, not an
    // error about to be reported. Checking the two HEADS before
    // reducing keeps the cost of that path where it was.
    if not reduce || not (reducible a || reducible b) then
        err (TypeError.mismatch a b)
    else
        match unify_go (term_peel (whnf scope locals a)) (term_peel (whnf scope locals b)) scope locals false {
            ok _ => ok a,
            err _ => err (TypeError.mismatch a b),
        }

/// Could `whnf` do anything here? Only two head shapes reduce: an
/// application (beta, once its head unfolds) and a free variable
/// naming a global def (delta). Everything else -- a `pi`, a sort, a
/// literal, a constructor, a bound variable -- is already in weak-head
/// normal form, and the overwhelming majority of real mismatches are
/// between two such rigid heads.
///
/// This over-approximates: a free variable that turns out to be a local
/// type parameter answers `true` and then does not reduce. That costs
/// one failed lookup, not a wrong answer.
def reducible (t : Term) : Bool :=
    match term_peel t {
        Term.app _ _ => true,
        Term.var idx _ => I64.beq idx sentinel,
        _ => false,
    }
