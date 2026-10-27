// Path combinators (univalence.md, Part D step 3).
//
// Each def is checked against its DECLARED type -- by the
// path-abstraction rule, which checks the body against the path's LINE and
// its two boundaries against the type's endpoints. Reaching that rule at
// all is what this branch had to buy: a path type SPELLED as a def
// (`Path A a b`) delta-unfolds to an application SPINE of the `pathp`
// primitive's name, not a `Term.cubical`, and `path_parts_of` only
// recognizes the latter. `whnf` now canonicalizes a saturated primitive
// spine (`as_cubical_type`, `lang/typecheck/whnf.mo`), so the
// abstraction dispatch, the boundary rewrite and `unify` all see one shape.
//
// The def-boundary comparison PR #133 added is still SKIPPED for these
// defs: `mentions_uninstantiated_typevar` treats a SKOLEMIZED local (a
// def's own type variable) as uninstantiated. Fixing that was built and
// corpus-run, and it turns `motes/shuttle/src/agent.mo` red on a
// pre-existing `solve_typevars` imprecision, so it is deferred and
// recorded in univalence.md rather than forced through here.
//
// The binders are written `(i : Cubical.I)` deliberately: `body_type_error`
// skips a body containing a `Term.hole` anywhere, and an UNANNOTATED
// `fn i => ...` carries one in its binder-type position. Measured, not
// assumed: with `fn i => ...` a deliberately wrong `refl` body
// (`fn i => Cubical.i0`) is still accepted. Recorded as an open hole in
// univalence.md rather than fixed here.
//
// `ap2` and `path_pair` are NOT here yet, and the reason is measured:
// both apply TWO paths at the same dimension (`g (p i) (q i)`), and
// `proofs/` has no `[affine] mode` table, i.e. the affine rule is
// enforced as an ERROR there -- a dimension used twice is rejected
// ("`i` : Cubical.I is used 2 times but is affine") because `Cubical.I`
// has no `Copy` instance. Giving the interval one is a separate decision
// (an instance body that duplicates a dimension, plus carrier matching
// against the `Term.cubical` interval node), recorded in univalence.md.

use proofs::equiv {Path}

/// The reflexivity path: the constant path at `a`.
pub def refl {A : Type} (a : A) : Path A a a :=
    fn (i : Cubical.I) => a

/// Path inversion: `sym p` walks `p` backwards by negating the dimension.
pub def sym {A : Type} {a : A} {b : A} (p : Path A a b) : Path A b a :=
    fn (i : Cubical.I) => p (Cubical.ineg i)

/// Application of a function to a path (`cong`).
pub def ap {A : Type} {B : Type} (f : A -> B) {a : A} {b : A}
    (p : Path A a b) : Path B (f a) (f b) :=
    fn (i : Cubical.I) => f (p i)

/// Dependent application: the result path lies over the line `B (p i)`.
pub def apd {A : Type} {B : A -> Type} (f : (x : A) -> B x)
    {a : A} {b : A} (p : Path A a b) :
    Cubical.PathP (fn x => B (p x)) (f a) (f b) :=
    fn (i : Cubical.I) => f (p i)
