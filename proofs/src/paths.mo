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
// The `funext` family (`funext`, `funext_dep`, `funext_inv`), `ap_refl` and
// `sym_sym` land on top of lambda conversion AND eta in `unify` (K2/K4),
// plus the applied-path boundary rewrite (`h x i0`, K5), all recorded in
// univalence.md. `funext`/`funext_dep` need all three; `ap_refl` and
// `sym_sym` compare a boundary against the unfold of a def (`ap`, `sym`),
// and `funext_inv` applies a path under an argument. The inner binder of
// `sym_sym` is named `i` to match `sym`'s own binder: `Similar` compares a
// bound variable's debug name, not only its index.
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
///
/// The implicit clauses come FIRST: the self-hosted parser restarts a def's
/// param list at every `{...}` clause, so an explicit param written before one
/// is dropped (and then auto-wrapped as an implicit forall by elaboration,
/// which silently changes the def's arity). `ap`/`apd` were the two defs that
/// had it the other way round.
pub def ap {A : Type} {B : Type} {a : A} {b : A}
    (f : A -> B) (p : Path A a b) : Path B (f a) (f b) :=
    fn (i : Cubical.I) => f (p i)

/// Dependent application: the result path lies over the line `B (p i)`.
pub def apd {A : Type} {B : A -> Type} {a : A} {b : A}
    (f : (x : A) -> B x) (p : Path A a b) :
    Cubical.PathP (fn x => B (p x)) (f a) (f b) :=
    fn (i : Cubical.I) => f (p i)

/// Function extensionality: pointwise paths give a path between functions.
pub def funext {A : Type} {B : Type} {f : A -> B} {g : A -> B}
    (h : (x : A) -> Path B (f x) (g x)) : Path (A -> B) f g :=
    fn (i : Cubical.I) => fn (x : A) => h x i

/// Dependent function extensionality: the codomain varies with the argument.
pub def funext_dep {A : Type} {B : A -> Type}
    {f : (x : A) -> B x} {g : (x : A) -> B x}
    (h : (x : A) -> Path (B x) (f x) (g x)) :
    Path ((x : A) -> B x) f g :=
    fn (i : Cubical.I) => fn (x : A) => h x i

/// The inverse direction: applying a path of functions pointwise.
pub def funext_inv {A : Type} {B : Type} {f : A -> B} {g : A -> B}
    (p : Path (A -> B) f g) : (x : A) -> Path B (f x) (g x) :=
    fn (x : A) => fn (i : Cubical.I) => p i x

/// `ap f` sends `refl a` to `refl (f a)`.
pub def ap_refl {A : Type} {B : Type} (f : A -> B) (a : A) :
    Path (Path B (f a) (f a)) (ap f (refl a)) (refl (f a)) :=
    fn (i : Cubical.I) => fn (j : Cubical.I) => f a

/// Double inversion is the identity. The INNER binder is deliberately named
/// `i`: the boundary comparison reaches `sym`'s own binder, also named `i`,
/// and `Similar` compares bound-variable names.
pub def sym_sym {A : Type} {a : A} {b : A} (p : Path A a b) :
    Path (Path A a b) (sym (sym p)) p :=
    fn (k : Cubical.I) => fn (i : Cubical.I) =>
        p (Cubical.ineg (Cubical.ineg i))
