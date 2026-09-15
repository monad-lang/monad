use lang.types {Similar, Term, TypeError, forall, hole, mismatch, pi, term_peel, type_}

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
/// `#[terminating]`: `term_peel` strictly removes wrappers, so the pair it
/// hands `unify_go` is smaller, but that is not a structural subterm the
/// checker can see.
#[terminating]
def unify (a : Term) (b : Term) : Result TypeError Term :=
    unify_go (term_peel a) (term_peel b)

#[partial]
def unify_go (a : Term) (b : Term) : Result TypeError Term :=
    match a {
        Term.hole => ok b,
        Term.pi arg1 ret1 => match b {
            Term.hole => ok a,
            Term.pi arg2 ret2 =>
                match unify arg1 arg2 {
                    ok _ => unify ret1 ret2,
                    err e => err e,
                },
            Term.forall _dbg _kind body2 => unify a body2,
            _ => err (TypeError.mismatch a b),
        },
        Term.type_ l1 => match b {
            Term.hole => ok a,
            Term.type_ l2 =>
                if I64.gt l1 l2 then
                    err (TypeError.mismatch a b)
                else
                    ok a,
            _ => err (TypeError.mismatch a b),
        },
        Term.forall _dbg _kind body1 => unify body1 b,
        _ => match b {
            Term.hole => ok a,
            Term.forall _dbg _kind body2 => unify a body2,
            _ =>
                if Similar.similar a b then
                    ok a
                else
                    err (TypeError.mismatch a b),
        },
    }
