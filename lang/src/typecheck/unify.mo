use lib::types {LocalScope, Scope, Similar, Term, TypeError, forall, hole, mismatch, pi, sentinel, term_peel, type_}
use lib::typecheck::whnf {whnf}

/// Structural type unification. Returns the unified type.
/// Holes match anything. Pi matches Pi structurally.
/// Sorts respect cumulativity (level ≤ expected_level).
/// Foralls are stripped before comparison.
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
        Term.pi arg1 ret1 => match b {
            Term.hole => ok a,
            Term.pi arg2 ret2 =>
                match unify arg1 arg2 scope locals {
                    ok _ => unify ret1 ret2 scope locals,
                    err e => err e,
                },
            Term.forall _dbg _kind body2 => unify a body2 scope locals,
            _ => unify_stuck a b scope locals reduce,
        },
        Term.type_ l1 => unify_sort a (SortLevel.concrete l1) b scope locals reduce,
        Term.sort l1 => unify_sort a l1 b scope locals reduce,
        Term.forall _dbg _kind body1 => unify body1 b scope locals,
        _ => match b {
            Term.hole => ok a,
            Term.forall _dbg _kind body2 => unify a body2 scope locals,
            _ =>
                if Similar.similar a b then
                    ok a
                else
                    unify_stuck a b scope locals reduce,
        },
    }

/// The sort arm, shared by both spellings of a sort term.
///
/// Cumulativity: `Sort l1 <= Sort l2` holds exactly when `l1 <= l2`, and the
/// comparison is DIRECTIONAL — `a` is the actual, `b` the expected, so
/// `Type` checked against `Prop` must fail while `Prop` against `Type`
/// succeeds. `unify` is the only place subsumption belongs; a call site
/// instantiating a level is solving, not subsuming.
///
/// `b` is read through `sort_level_of`, so `Term.type_ n` and
/// `Term.sort (concrete n)` compare as the same sort. That is what lets the
/// parser emit one spelling and the checker's own constructions use the
/// other without every comparison between them turning into a mismatch.
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
