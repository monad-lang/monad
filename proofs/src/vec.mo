// Basic `Vec` facts.
//
// `Vec` is INDEXED (`nil : Vec Nat.zero A`, `cons : … -> Vec (Nat.succ len) A`).
// The self-hosted checker solves a constructor's declared index against the
// scrutinee's (`lang/src/typecheck/ctor_refine.mo`): in `vtail`'s `cons` arm
// the tail is `Vec n A`, `vhead` needs no `nil` arm (it can never match), and
// in `vappend` each arm's expected length is refined (`Nat.add Nat.zero n` in
// the `nil` arm). Constructor INTRODUCTION is not yet checked against an
// indexed expected type (`Vec.nil : Vec 1 I64` is accepted), so these
// functions' `cons` arms are typed by their fields, not their length; that is
// Stage 3c. These facts exercise constructor typing and definitional
// (iota/delta) reduction.

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

/// Head of a non-empty vector. `Vec.nil` cannot have type
/// `Vec (Nat.succ n) A`, so the match is exhaustive without that arm.
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

/// Tail of a non-empty vector, one shorter.
pub def vtail {n : Nat} {A : Type} (v : Vec (Nat.succ n) A) : Vec n A :=
    match v {
        Vec.cons _ t => t,
    }

/// Map over every element; the length is unchanged.
pub def vmap {n : Nat} {A : Type} {B : Type} (f : A -> B) (v : Vec n A) : Vec n B :=
    match v {
        Vec.nil => Vec.nil,
        Vec.cons h t => Vec.cons (f h) (vmap f t),
    }

/// Concatenation; the lengths add.
pub def vappend {m : Nat} {n : Nat} {A : Type} (v : Vec m A) (w : Vec n A) : Vec (Nat.add m n) A :=
    match v {
        Vec.nil => w,
        Vec.cons h t => Vec.cons h (vappend t w),
    }

def vec12 : Vec (Nat.succ (Nat.succ Nat.zero)) I64 := Vec.cons 1 (Vec.cons 2 (vec_nil I64))

#[test]
def test_vtail_drops_the_head : Bool :=
    I64.beq (vhead (vtail vec12)) 2

#[test]
def test_vmap_maps_each_element : Bool :=
    I64.beq (vhead (vmap (fn (x : I64) => x * 10) vec12)) 10

#[test]
def test_vappend_keeps_the_order : Bool :=
    let both : Vec (Nat.add (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero))) I64 := vappend vec12 vec12 in
    I64.beq (vlength_i64 both) 4

/// The length as an `I64`, for the executed tests.
def vlength_i64 {n : Nat} {A : Type} (v : Vec n A) : I64 :=
    match v {
        Vec.nil => 0,
        Vec.cons _ t => 1 + vlength_i64 t,
    }
