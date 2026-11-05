// Basic `Vec` facts.
//
// `Vec` is INDEXED (`nil : Vec Nat.zero A`, `cons : … -> Vec (Nat.succ len) A`),
// and the self-hosted dependent-match gate currently accepts only non-indexed
// inductives. Indexed induction (`Vec.length`-style proofs over an arbitrary
// length) is therefore out of scope here; these facts exercise constructor
// typing and definitional (iota/delta) reduction, which the checker does
// support.

use proofs::equiv {Path}
use proofs::paths {refl}

/// A non-dependent `Vec.length`, by an ordinary match over both constructors.
pub def vlength {n : Nat} {A : Type} (v : Vec n A) : Nat :=
    match v {
        Vec.nil => Nat.zero,
        Vec.cons _ t => Nat.succ (vlength t),
    }

/// The empty vector's path, written as a path lambda: `refl Vec.nil` leaves
/// the element type and `Path`'s universe under-determined in this position
/// (measured: `Path Prop Vec.nil Vec.nil`), while the lambda is checked
/// against the declared line and boundaries directly.
#[proof]
pub def nil_refl {A : Type} : Path (Vec Nat.zero A) Vec.nil Vec.nil :=
    fn (i : Cubical.I) => Vec.nil

/// A constructed vector's path is `refl`.
#[proof]
pub def cons_refl {n : Nat} {A : Type} (a : A) (v : Vec n A) :
    Path (Vec (Nat.succ n) A) (Vec.cons a v) (Vec.cons a v) :=
    refl (Vec.cons a v)

/// The empty vector at an explicit element type. Written as a `def` rather
/// than an ascription: `Vec.nil`'s own type is expected-type driven, and a
/// named def gives it a fully-known type without one.
pub def vec_nil (A : Type) : Vec Nat.zero A := Vec.nil

/// `vlength` of the empty vector is zero, definitionally. A path lambda for
/// the same reason as `nil_refl` (the boundary is a delta/iota redex).
#[proof]
pub def vlength_nil {A : Type} :
    Path Nat (vlength (vec_nil A)) Nat.zero :=
    fn (i : Cubical.I) => Nat.zero

/// `vlength` of a cons is the successor of the tail's length, definitionally.
#[proof]
pub def vlength_cons {n : Nat} {A : Type} (a : A) (v : Vec n A) :
    Path Nat (vlength (Vec.cons a v)) (Nat.succ (vlength v)) :=
    refl (Nat.succ (vlength v))
