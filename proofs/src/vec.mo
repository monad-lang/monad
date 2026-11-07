// Basic `Vec` facts.
//
// `Vec` is INDEXED (`nil : Vec Nat.zero A`, `cons : … -> Vec (Nat.succ len) A`).
// The self-hosted checker now checks the index argument of a `Vec` type
// application (`Vec 3 I64`, negative indices) and normalizes small literals
// to unary, but it does NOT yet refine a match's expected type (or a
// constructor's declared return) from the constructor's index. `vhead` can
// omit the impossible `nil` arm behind `#[allow_incomplete_match]` because
// its result does not mention the index; `vtail` (`Vec n A`) and the
// `vappend`/`vmap` length equations are blocked on that refinement. Indexed induction over an abstract `n`
// (the `vappend`/`vmap` length equations) remains out of scope; these facts
// exercise constructor typing and definitional (iota/delta) reduction.

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

/// Head of a non-empty vector. The `nil` arm is impossible for
/// `Vec (Nat.succ n) A`; the checker cannot prove that yet, so the omission
/// is explicit. A wrong-length value cannot reach this function.
#[allow_incomplete_match "Vec (Nat.succ n) A is never Vec.nil"]
pub def vhead {n : Nat} {A : Type} (v : Vec (Nat.succ n) A) : A :=
    match v {
        Vec.cons a _ => a,
    }

#[test]
def test_vhead_cons : Bool :=
    I64.beq (vhead (Vec.cons 7 (Vec.nil : Vec Nat.zero I64))) 7

#[proof]
pub def vhead_cons {n : Nat} {A : Type} (a : A) (v : Vec n A) :
    Path A (vhead (Vec.cons a v)) a :=
    refl a
