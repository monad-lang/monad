// `LawfulMonad`: a class whose instances must PROVE the three monad laws.
//
// The class lives in `proofs/` because the laws are `Path` equalities and
// `init/` may not import `proofs/`. Its result sort is `Prop` (the class-head
// Sort clause): the laws are propositions.
//
// The operations are EXPLICIT class parameters, and their type arguments are
// EXPLICIT Pi binders. Both are forced by measurement:
//
//   * the self-hosted checker does not reduce a class-METHOD call in a type,
//     so `Path (Id B) (Monad.bind (Monad.pure a) f) (f a)` can never convert
//     to `Path (Id B) (f a) (f a)` and its law is unprovable;
//   * an implicit binder inside a class parameter's type (`bind : {A : Type}
//     -> ...`) is not parseable (the class head fails to parse), so the
//     operations take `(A : Type)` explicitly.
//
// Right identity and associativity case-split on `Id`'s single constructor.
// A direct `match m { … }` checks the arm body against a derived motive the
// checker leaves unreduced (`Id.bind … (id a) …` never converts), so the
// proofs go through an EXPLICIT eliminator with a named family -- the same
// recipe `proofs/src/nat.mo` documents.
use proofs::equiv {Path}
use proofs::paths {refl}

/// A monad whose operations satisfy the three laws. `bind`/`pure` are the
/// instance's own operations, passed explicitly.
pub class [Monad M] LawfulMonad (M : Type -> Type)
    (bind : (A : Type) -> (B : Type) -> (a : M A) -> (f : A -> M B) -> M B)
    (pure : (A : Type) -> (a : A) -> M A) : Prop {
    /// `bind (pure a) f = f a`.
    def left_identity (a : A) (f : A -> M B) :
        Path (M B) (bind A B (pure A a) f) (f a)

    /// `bind m pure = m`.
    def right_identity (m : M A) :
        Path (M A) (bind A A m (pure A)) m

    /// `bind (bind m f) g = bind m (fn x => bind (f x) g)`.
    def associative (m : M A) (f : A -> M B) (g : B -> M C) :
        Path (M C) (bind A C (bind A B m f) g)
            (bind A C m (fn x => bind B C (f x) g))
}

/// The identity monad's `pure`, as a named def so the laws can reduce it.
pub def Id.pure (A : Type) (a : A) : Id A := Id.id a

/// The identity monad's `bind`, as a named def so the laws can reduce it.
pub def Id.bind (A : Type) (B : Type) (m : Id A) (f : A -> Id B) : Id B :=
    match m { Id.id a => f a }

/// `Id`'s explicit eliminator: an arbitrary family over `Id A`, supplied by
/// its value at the single constructor. Mirrors `nat_elim`/`list_elim`.
pub def Id.elim {A : Type} (P : Id A -> Type) (h : (a : A) -> P (Id.id a))
    (m : Id A) : P m :=
    match m { Id.id a => h a }

/// The right-identity family (`#[proof]`: it mentions `m` twice).
#[proof]
pub def Id.right_fam {A : Type} (m : Id A) : Type :=
    Path (Id A) (Id.bind A A m (Id.pure A)) m

/// The associativity family (`#[proof]`: it mentions `m`/`g` twice).
#[proof]
pub def Id.assoc_fam {A B C : Type} (f : A -> Id B) (g : B -> Id C) (m : Id A) : Type :=
    Path (Id C) (Id.bind A C (Id.bind A B m f) g)
        (Id.bind A C m (fn x => Id.bind B C (f x) g))

/// `Id` is a lawful monad for its own `bind`/`pure`. The instance's method
/// bodies are the checked proofs (the self-hosted checker verifies them).
pub instance LawfulMonad Id Id.bind Id.pure {
    /// `bind (pure a) f` reduces to `f a`.
    def left_identity (a : A) (f : A -> Id B) :
        Path (Id B) (Id.bind A B (Id.pure A a) f) (f a) :=
        refl (f a)

    /// Match the single constructor; both sides reduce to `id a`.
    def right_identity (m : Id A) :
        Path (Id A) (Id.bind A A m (Id.pure A)) m :=
        Id.elim Id.right_fam (fn a => refl (Id.id a)) m

    /// Match the single constructor; both sides reduce to `bind (f a) g`.
    /// `f`/`g` are read twice (family + step), so they are shared through
    /// `Shared.get`, whose borrowed reads the affine rule exempts.
    def associative (m : Id A) (f : A -> Id B) (g : B -> Id C) :
        Path (Id C) (Id.bind A C (Id.bind A B m f) g)
            (Id.bind A C m (fn x => Id.bind B C (f x) g)) :=
        let fs : Shared (A -> Id B) := Shared.of f in
        let gs : Shared (B -> Id C) := Shared.of g in
        Id.elim (Id.assoc_fam (Shared.get fs) (Shared.get gs))
            (fn a => refl (Id.bind B C (Shared.get fs a) (Shared.get gs))) m
}
