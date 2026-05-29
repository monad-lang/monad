use lang.types
open types

/// Structural type unification. Returns the unified type.
/// Holes match anything. Pi matches Pi structurally.
/// Sorts respect cumulativity (level ≤ expected_level).
/// Foralls are stripped before comparison.
def unify (a : Term) (b : Term) : Result TypeError Term :=
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
