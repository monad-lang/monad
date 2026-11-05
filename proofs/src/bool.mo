// Basic `Bool` theorems.
//
// `Bool` is a non-indexed, nullary inductive, so each theorem is an ordinary
// dependent `match` whose result type mentions the scrutinee: the checker's
// dependent-match fallback refines each arm and reduces `Bool.not`/`and`/`or`
// by delta + iota. No induction is needed.

use proofs::equiv {Path}
use proofs::paths {refl}

/// Double negation is the identity.
#[proof]
pub def not_not (b : Bool) : Path Bool (Bool.not (Bool.not b)) b :=
    match b {
        Bool.true => refl Bool.true,
        Bool.false => refl Bool.false,
    }

/// `true` is a right identity for `&&`.
#[proof]
pub def and_true (b : Bool) : Path Bool (Bool.and b Bool.true) b :=
    match b {
        Bool.true => refl Bool.true,
        Bool.false => refl Bool.false,
    }

/// `false` is a right identity for `||`.
#[proof]
pub def or_false (b : Bool) : Path Bool (Bool.or b Bool.false) b :=
    match b {
        Bool.true => refl Bool.true,
        Bool.false => refl Bool.false,
    }
