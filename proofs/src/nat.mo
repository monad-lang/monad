// Basic `Nat` theorems.
//
// Recursive induction is written through an EXPLICIT eliminator with a NAMED
// type family, not a direct recursive `match`:
//
//   * the dependent-match fallback needs the result type to be a type-level
//     function of the scrutinee that the checker can see, and a direct
//     self-call inside the arm loses the level instantiation of `Path`
//     (measured: `expected Nat, found Prop`);
//   * the family is a named def, so `nat_elim fam …` instantiates `P` once.
//
// `#[proof]` gives the defs the affine exemption: the eliminator's step uses
// its predecessor twice (`hs k (nat_elim … k)`), and a family that mentions
// its argument twice would otherwise be rejected as affine. The bodies are
// still fully type-checked; the marker only licenses sharing.

use proofs::equiv {Path}
use proofs::paths {refl, ap}

/// Structural induction over `Nat`, into an arbitrary type family.
#[proof]
pub def nat_elim (P : Nat -> Type) (hz : P Nat.zero)
    (hs : (k : Nat) -> P k -> P (Nat.succ k)) (n : Nat) : P n :=
    match n {
        Nat.zero => hz,
        Nat.succ k => hs k (nat_elim P hz hs k),
    }

/// `n + 0 = n`.
#[proof]
pub def add_zero_fam (n : Nat) : Type :=
    Path Nat (Nat.add n Nat.zero) n

#[proof]
pub def add_zero (n : Nat) : Path Nat (Nat.add n Nat.zero) n :=
    nat_elim add_zero_fam (refl Nat.zero) (fn k ih => ap Nat.succ ih) n

/// `0 + n = n` holds definitionally.
#[proof]
pub def zero_add (n : Nat) : Path Nat (Nat.add Nat.zero n) n :=
    refl n

/// Addition is associative.
#[proof]
pub def add_assoc_fam (b : Nat) (c : Nat) (a : Nat) : Type :=
    Path Nat (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c))

#[proof]
pub def add_assoc (a : Nat) (b : Nat) (c : Nat) :
    Path Nat (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c)) :=
    nat_elim (add_assoc_fam b c) (refl (Nat.add b c))
        (fn k ih => ap Nat.succ ih) a
