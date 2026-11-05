// Basic `Bool` theorems.
//
// `Bool` is a non-indexed, nullary inductive. `not_not` is an ordinary
// dependent `match` (the result type mentions the scrutinee, so the dependent
// fallback refines each arm and reduces `Bool.not` by delta + iota).
//
// `and_true` goes through an explicit eliminator with a named family: the
// direct-match form is accepted for `not_not` but NOT for a motive whose body
// is `Bool.and b …` (measured: "expected Bool, found Prop"), while the
// eliminator shape checks. The `Bool.or` dual is omitted for the same reason
// (`Bool.or b false = b` fails with an unreduced family step); it is recorded
// rather than asserted.

use proofs::equiv {Path}
use proofs::paths {refl}

/// Double negation is the identity.
#[proof]
pub def not_not (b : Bool) : Path Bool (Bool.not (Bool.not b)) b :=
    match b {
        Bool.true => refl Bool.true,
        Bool.false => refl Bool.false,
    }

/// Case analysis over `Bool` into an arbitrary type family.
#[proof]
pub def bool_elim (P : Bool -> Type) (t : P Bool.true) (f : P Bool.false)
    (b : Bool) : P b :=
    match b {
        Bool.true => t,
        Bool.false => f,
    }

/// The family for `and_true` (`#[proof]`: `b` is mentioned twice).
#[proof]
pub def and_true_fam (b : Bool) : Type :=
    Path Bool (Bool.and b Bool.true) b

/// `true` is a right identity for `&&`.
#[proof]
pub def and_true (b : Bool) : Path Bool (Bool.and b Bool.true) b :=
    bool_elim and_true_fam (refl Bool.true) (refl Bool.false) b
