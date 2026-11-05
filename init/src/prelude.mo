pub type Any {
    any {A : Type} (value : A)
}

pub class Functor (F : Type -> Type) {
    def map (f : A -> B) : (F A) -> F B
}

pub class FromListLiteral (L : Type -> Type := List) {
    def cons (a : A) (L A) : L A
    def empty : L A
}

/// The arithmetic operators dispatch through the HETEROGENEOUS classes
/// (`HAdd A B C`: operands and result may differ), so a mote can declare
/// a genuinely mixed instance. The symmetric case -- every built-in
/// numeric type -- is the homogeneous class (`Add A`), reached through
/// one bridge per operator: `instance [Add A] HAdd A A A`. A type gets
/// `+` by declaring `Add T`; nothing declares `HAdd T T T` for a
/// symmetric operation. The bridges run one way only: an `Add A` derived
/// from `HAdd A A A` would make the pair mutually recursive (a dictionary
/// that builds itself), so there is none.

/// Heterogeneous addition
pub class HAdd A B C {
    def add : A -> B -> C
}

/// Homogeneous addition
pub class Add A {
    def add : A -> A -> A
}

pub instance [Add A] HAdd A A A {
    def add (a b : A) : A := Add.add a b
}

/// Heterogeneous subtraction
pub class HSub A B C {
    def sub : A -> B -> C
}

/// Homogeneous subtraction
pub class Sub A {
    def sub : A -> A -> A
}

pub instance [Sub A] HSub A A A {
    def sub (a b : A) : A := Sub.sub a b
}

/// Heterogeneous multiplication
pub class HMul A B C {
    def mul : A -> B -> C
}

/// Homogeneous multiplication
pub class Mul A {
    def mul : A -> A -> A
}

pub instance [Mul A] HMul A A A {
    def mul (a b : A) : A := Mul.mul a b
}

/// Heterogeneous division
pub class HDiv A B C {
    def div : A -> B -> C
}

/// Homogeneous division
pub class Div A {
    def div : A -> A -> A
}

pub instance [Div A] HDiv A A A {
    def div (a b : A) : A := Div.div a b
}

pub infix (+) := HAdd.add

pub infix (/) := HDiv.div

pub infix (*) := HMul.mul

pub infix (-) := HSub.sub

pub class [Functor F] Applicative (F : Type -> Type) {
    def pure : A -> F A
    def apply : F (A -> B) -> F A -> F B
}

pub class [Applicative M] Monad (M : Type -> Type) {
    def bind (a : M A) (f : A -> M B) : M B
    def pure : A -> M A
}

pub infix (>>=) := Monad.bind

/// Dual of `Monad`: `extract` pulls the value out of a context; `duplicate`
/// and `extend` push the context inwards. All three are required -- the usual
/// `extend f = map f . duplicate` default would need a `Functor` superclass
/// constraint, and a superclass constraint gets no slot in the dictionary.
pub class Comonad (W : Type -> Type) {
    def extract (W A) : A
    def duplicate (W A) : W (W A)
    def extend (f : W A -> B) (W A) : W B
}

/// State monad: thread state S through a monad M.
/// Single-param class (M only) — S is an implicit forall variable,
/// like Map's K/V, so `KnownInstances` can key on the monad's concrete
/// head (e.g. `State`), not a variable.
pub class MonadState (M : Type -> Type) {
    def get : M S
    def set (s : S) : M Unit
    def modify_get (f : S -> Pair S A) : M A

    /// Modify the state and return unit
    def modify (f : S -> S) : M Unit :=
        modify_get (fn s => Pair.pair (f s) unit)

    /// Get the state, apply a function, and return the result
    def get_map (f : S -> A) : M A :=
        modify_get (fn s => Pair.pair s (f s))
}

/// Lift computations from monad `m` into monad `n`
pub class MonadLift (m : Type -> Type) (n : Type -> Type) {
    def monad_lift (a : m A) : n A
}

/// Transitive monad lift. The reflexive instance (lifting from
/// `m` to `m`) is the identity below; for other pairs, provide
/// an instance that delegates to `MonadLift`.
pub class MonadLiftT (m : Type -> Type) (n : Type -> Type) {
    def monad_lift_t (a : m A) : n A
}

/// Reflexive: lifting from m to m is the identity
pub instance MonadLiftT m m {
    def monad_lift_t (a : m A) : m A := a
}

/// `Void` is the deliberate exception to the witness rule: it IS the empty
/// type (`False`). Nothing may inhabit it, and matching on it is the absurd
/// eliminator. It is not an opaque VALUE type, so it carries no witness.
pub type Void {}

/// `Inhabited a` — `a` has a canonical value. A class (instance-resolved),
/// so generic code can require one implicitly.
///
/// The class's own result sort is `Sort (max 1 u)`: the dictionary type lives
/// one universe above its carrier at least. The class head now carries that
/// clause for real (`Class.sort`), and `check_class_with_scope` rejects a
/// non-sort kind.
pub class Inhabited {u : Universe} (a : Sort u) : Sort (max 1 u) {
    def default : a
}

/// `NonEmpty a` — the proposition that `a` has SOME value. Proof-level
/// (`Pred` is the `Prop` alias), so it is erased and proof-irrelevant. Use
/// it where only existence matters; use `Inhabited` when a default value is
/// wanted.
pub type NonEmpty {u : Universe} (a : Sort u) : Pred {
    nonempty (witness : a),
}

/// UTF8 string
pub type String {
    of_bytes (List U8)
}

/// UTF8 code point
pub type Char {
    of_bytes (List U8)
}

pub class ToString A {
    def to_string (a : A) : String
}

/// Primitive number types.
///
/// Each is an OPAQUE native-backed type: an inductive with exactly one
/// nullary WITNESS constructor. A type with no constructors is the empty
/// type (`False`), and a native returning one would be asserting an
/// inhabitant of `False` — so every opaque value type declares a witness.
/// `#[opaque]` makes the witness unreferenceable: it may be neither
/// constructed nor matched, which is what keeps the type abstract and its
/// representation native. Values come only from the native operations.
#[opaque]
pub type I64 { i64_witness }
#[opaque]
pub type I32 { i32_witness }
#[opaque]
pub type I16 { i16_witness }
#[opaque]
pub type I8 { i8_witness }

#[opaque]
pub type U64 { u64_witness }
#[opaque]
pub type U32 { u32_witness }
#[opaque]
pub type U16 { u16_witness }
#[opaque]
pub type U8 { u8_witness }

#[opaque]
pub type F64 { f64_witness }
#[opaque]
pub type F32 { f32_witness }

/// Opaque C pointer for the `#[extern "c"]` FFI. A `Ptr` value is the
/// raw machine word under every backend; never match, compare or print
/// one (the `FdStream` convention, std/src/stream.mo). The witness keeps
/// the type inhabited; `#[opaque]` keeps it abstract.
#[opaque]
pub type Ptr { ptr_witness }

/// The NULL pointer — `SSL_set_verify`'s callback argument is the first
/// caller (motes/tls).
#[native "ptr_null"]
pub def Ptr.null : Ptr

/// The fixed `(void*)-1` sentinel (SQLite's `SQLITE_TRANSIENT` is one
/// user). It takes no input, so unlike a general I64-to-Ptr conversion it
/// cannot produce an arbitrary address.
#[native "ptr_minus_one"]
pub def Ptr.minus_one : Ptr

pub type Unit {
    unit
}

// TODO: the `open ... {...}` filters below are hand-verified against
// bare usage across the WHOLE codebase, not just this file — prelude's
// own `open`s are unconditionally chained into every other file's scope
// (see `GlobalScopeData::from_module`), so a filter based on what THIS
// file alone references (what `monad-rs organize-imports` computes by
// default) would under-count and break other files that rely on these
// names being ambiently bare (e.g. `unit`, `not`, `err`). Re-verify by
// hand if this file's `open`s ever change.
open Unit {unit}

pub type Bool {
    true,
    false
}

open Bool {and, false, not, or, true}

/// Trivially true proposition (unit in Prop)
pub type True : Prop {
    trivial
}

open True {trivial}

/// Propositional equality: Eq A a b lives in Prop (Sort 0)
pub type Eq (A : Sort 1) (a : A) (b : A) : Prop {
    refl : Eq A a a
}

/// Native J eliminator for propositional equality
#[native "eq_rec"]
pub def Eq.rec (A : Sort 1) (a : A) (P : (b : A) -> Eq A a b -> Sort 1)
    (h : P a (Eq.refl a)) (b : A) (e : Eq A a b) : P b e

/// Equals
pub class BEq A {
    def beq : A -> A -> Bool

    /// Logical negation of `beq`, as a class DEFAULT: an instance only
    /// implements `beq`. The self-hosted compiler splices this body into an
    /// instance that omits it (`promote_methods`).
    def not_beq (a : A) (b : A) : Bool := Bool.not (BEq.beq a b)
}

pub instance BEq Bool {
    def beq (a b : Bool) : Bool :=
        if a then b
        else (Bool.not b)
}

pub infix (==) := BEq.beq

pub infix (!=) := BEq.not_beq

/// Ordered comparison.
///
/// `lte`/`gte` are required methods rather than class defaults: the Rust
/// host's checked dictionary path refuses an instance that omits a declared
/// method whose implementation is a default (`check_one_instance_new` in
/// rust/core/src/core_check_module.rs), falling back to an unchecked path. Every
/// instance therefore states both. They mean `not gt` / `not lt`, the
/// total-order reading `BOrd` already assumes.
pub class BOrd A {
    def lt (a b : A) : Bool
    def gt (a b : A) : Bool
    def lte (a b : A) : Bool
    def gte (a b : A) : Bool
}

pub infix (<) := BOrd.lt

/// `a <= b`, i.e. `not (a > b)`.
pub infix (<=) := BOrd.lte

/// `a >= b`, i.e. `not (a < b)`.
pub infix (>=) := BOrd.gte

pub infix (>) := BOrd.gt

pub instance BOrd Bool {
    def lt (a b : Bool) : Bool :=
        if a then false
        else b

    def gt (a b : Bool) : Bool :=
        if a then Bool.not b
        else false

    // false <= anything; true <= b exactly when b is true.
    def lte (a b : Bool) : Bool :=
        if a then b
        else true

    // true >= anything; false >= b exactly when b is false.
    def gte (a b : Bool) : Bool :=
        if a then true
        else Bool.not b
}

/// Hashable: produce a hash value for an element.
pub class Hashable A {
    def hash (a : A) : U64
}

pub type DefaultValue (A : Type) (default : A) {
    default
}

pub def Bool.not (b : Bool) : Bool := if b then false else true

pub def Bool.and (a b : Bool) : Bool := if a then b else false

pub infix (&&) := Bool.and

pub def Bool.or (a b : Bool) : Bool := if a then true else b

pub infix (||) := Bool.or

pub type Result E A {
    ok (a : A),
    err (e : E)
}

/// Whether `r` is `Result.ok` -- for a caller that checks an effect's
/// outcome (a test asserting a write landed) without needing its value.
pub def Result.is_ok {E A : Type} (r : Result E A) : Bool :=
    match r {
        Result.ok _ => true,
        Result.err _ => false
    }

pub type Pair A B {
    pair (first : A) (second : B)
}

/// Dependent pair: the second component's TYPE may depend on the first
/// component's VALUE -- e.g. `Sigma Nat (fn n => Vec n A)` pairs a
/// length with a vector of exactly that length.
///
/// The non-dependent `Pair A B` above is the special case
/// `Sigma A (fn _ => B)`. Both are kept: recovering `fn _ => B` at every
/// tuple literal would need higher-order unification, so `Pair` remains
/// what the tuple syntax desugars to.
///
/// `snd`'s declared type applies `B` to the EARLIER field `fst`. That
/// shape was unrepresentable until constructor parameter lists were made
/// to bind; before that the mention dangled and was silently generalized
/// into an unrelated implicit.
/// Dependent pairs. The result universe is a FREE level `w`, so the same
/// inductive serves both a data `Sigma` (instantiated at `Sort (max u v)`)
/// and the propositional `Exists` below (instantiated at `Sort 0`, where
/// `Prop`'s impredicativity lets a `Type`-level first component sit inside a
/// `Prop` pair).
///
/// The level clauses are deliberately OMITTED (`type Sigma (A : Sort u) …`
/// rather than `{u} {v} {w}`): levels are name-keyed and survive by mention
/// in `Sort u`/`Sort v`/`Sort w`, and one name per `{...}` clause is the
/// grammar both compilers share. The Rust host has no level variables; it
/// approximates a bare symbolic result sort to the bottom universe.
pub type Sigma (A : Sort u) (B : A -> Sort v) : Sort w {
    dpair (fst : A) (snd : B fst)
}

/// Existential quantification -- `Sigma` instantiated at `Prop`.
///
/// This is now a def alias: `Sigma A P` is a dependent pair whose result
/// level is solved by the expected `Prop`, so the pair itself lands in
/// `Sort 0`. One constructor (`Sigma.dpair`) and one set of projections
/// serve both `Sigma` and `Exists`.
pub def Exists (A : Type) (P : A -> Prop) : Prop := Sigma A P

/// First projection. Non-dependent, so ordinary match typing suffices.
///
/// Constructing `Sigma.dpair a b` requires `B a` to reduce, i.e. conversion
/// checking, which the self-hosted checker has. The Rust host can now TYPE a
/// generic `Sigma A B` application (its kind's Pi binders carry names), but
/// it still does not construct one; construction is covered by source-string
/// tests in `lang/src/tests/typecheck_examples_tests.mo`.
///
/// The second projection `Sigma.snd (p : Sigma A B) : B (Sigma.fst p)` lives
/// in `proofs/src/dependent.mo` (`sigma_snd`): checking it needs the arm's
/// expected type to see the scrutinee refined to `Sigma.dpair a b`, which is
/// the dependent-match rule, not a prelude concern.
pub def Sigma.fst {A : Type} {B : A -> Type} (p : Sigma A B) : A :=
    match p { Sigma.dpair a _ => a }

open Result {err, ok}

pub type Option A {
    some (a : A),
    none
}

open Option {none, some}

pub def Option.get_or_default (default : A) (self : Option A) : A :=
    match self {
        some a => a,
        none => default
    }

pub type Nat {
    zero,
    succ (n : Nat)
}

pub def Nat.add (a b : Nat) : Nat :=
    match a {
        zero => b,
        succ n => Nat.succ (Nat.add n b)
    }

pub def Nat.sub (a b : Nat) : Nat :=
    match b {
        zero => a,
        succ n => match a {
            zero => Nat.zero,
            succ m => Nat.sub m n
        }
    }

pub def Nat.mul (a b : Nat) : Nat :=
    match a {
        zero => Nat.zero,
        succ n => Nat.add b (Nat.mul n b)
    }

pub def Nat.eq (a b : Nat) : Bool :=
    match a {
        zero => match b {
            zero => true,
            succ _ => false
        },
        succ n => match b {
            zero => false,
            succ m => Nat.eq n m
        }
    }

pub instance BEq Nat {
    def beq (a b : Nat) : Bool := Nat.eq a b
}

pub instance Add Nat {
    def add (a b : Nat) : Nat := Nat.add a b
}

pub instance Sub Nat {
    def sub (a b : Nat) : Nat := Nat.sub a b
}

pub def Lens [Functor F] {F : Type -> Type} (S : Type) (T : Type) (A : Type) (B : Type) : Type :=
    (A -> F B) -> S -> F T

pub type List A {
    empty,
    cons (a : A) (List A) : List A
}

pub instance FromListLiteral List {
    def cons (a : A) (l : List A) : List A := List.cons a l
    def empty : List A := List.empty
}

pub def List.is_empty (self : List A) : Bool :=
    match self {
        empty => true,
        cons a tail => false,
        _ => true
    }

pub def List.append (a b : List A) : List A :=
    match a {
        empty => b,
        cons el_a tail => List.cons el_a (List.append tail b),
        _ => b
    }

/// Append b to value a
pub class Append A {
    def append (a b : A) : A
}

pub infix (++) := Append.append

pub def List.first (self : List A) : Option A :=
    match self {
        empty => none,
        cons a tail => some a,
        _ => none
    }
pub def List.last (self : List A) : Option A :=
    match self {
        empty => none,
        cons a tail => if List.is_empty tail
            then some a
            else List.last tail,
        _ => none
    }
pub def List.flatten (self : List (List A)) : List A :=
    match self {
        empty => List.empty,
        cons list tail => List.append list (List.flatten tail),
        _ => List.empty
    }

pub def List.tail (l : List A) : List A :=
    match l {
        empty => List.empty,
        cons a tail => tail,
        _ => List.empty
    }

pub def List.map (f : A -> B) (self : List A) : List B :=
    match self {
        empty => List.empty,
        cons a tail => List.cons (f a) (List.map f tail),
        _ => List.empty
    }

pub instance Functor List {
    // `List.map` (not the recursive `Functor.map`) -- a match-arm PATTERN-
    // bound variable (`tail`, from `cons a tail => ...`) is never added to
    // `env` by `resolve_class_call_term`'s term walker (`lang/scope.mo`,
    // only `Term.lam`-introduced bindings are, see its own doc comment) --
    // a distinct gap from the bare-local-var one already fixed, caught by
    // the new fail-fast check (`no instance found for 'Functor.map'`) this
    // instance's own recursive call had been silently hitting. `List.map`
    // (just above) is the identical concrete implementation, already
    // correct and non-generic -- reuse it instead of chasing this gap here.
    def map (f : A -> B) (self : List A) : List B :=
        match self {
            empty => List.empty,
            cons a tail => List.cons (f a) (List.map f tail),
            _ => List.empty
        }
}

/// A length-indexed vector: Vec len A is a list of exactly len elements of type A
pub type Vec (len : Nat) A {
    nil : Vec Nat.zero A,
    cons (head : A) (tail : Vec len A) : Vec (Nat.succ len) A
}

pub def fun_apply (f : A -> B) (a : A) : B := f a

pub infix (<|) := fun_apply

pub def apply_fun (a : A) (f : A -> B) : B := f a

pub infix (|>) := apply_fun

/// Indexed monad: M I J A
/// I = initial index, J = final index, A = value
pub class IndexedMonad (M : Type -> Type -> Type -> Type) {
    def pure (a : A) : M I I A
    def bind (a : M I J A) (f : A -> M J K B) : M I K B

    /// Map across the value (preserving indices)
    def map (f : A -> B) (ma : M I J A) : M I J B :=
        bind ma (fn a => pure (f a))

    /// Sequence two actions, discarding the first value
    def and_then (first : M I J A) (second : M J K B) : M I K B :=
        bind first (fn _ => second)

    /// Lift a pure value into the indexed monad at any index
    def lift (a : A) : M I I A := pure a
}

/// Any `IndexedMonad M` at equal indices (`M I I`) is a regular `Monad`.
/// This bridge instance provides `Monad (M I I)` for every `IndexedMonad M`,
/// enabling do-notation for indexed monads without type-checker changes.
pub instance {I : Type} [IndexedMonad M] Monad (M I I) {
    def pure (a : A) : M I I A := IndexedMonad.pure a
    def bind (a : M I I A) (f : A -> M I I B) : M I I B := IndexedMonad.bind a f
}

/// Indexed state monad: thread state S through an indexed monad M.
/// State operations preserve the index (M I I), so they can be
/// sequenced in any position without changing the protocol state.
/// Single-param class (M only) — S is implicit forall, same as
/// `MonadState` above.
pub class IndexedMonadState (M : Type -> Type -> Type -> Type) {
    def get : M I I S
    def set (s : S) : M I I Unit
    def modify_get (f : S -> Pair S A) : M I I A
}

/// Lift computations from indexed monad `m` into indexed monad `n`
pub class IndexedMonadLift (m : Type -> Type -> Type -> Type) (n : Type -> Type -> Type -> Type) {
    def monad_lift (a : m I J A) : n I J A
}

// The cubical interval and its operations (univalence.md Stages 1-5, plus
// Stage 6b's `is_one i1` witness and Stage 6b-ii's `Glue`), as BODY-LESS
// marker defs inside a `with Cubical` block. The
// `#[cubical "..."]` MARKER, never the bare spelling, is what binds:
// `build_scope_def` (lang/src/scope.mo) enters the def's prefixed name
// into `ScopeData.cubical_prims`, and the checker rewrites a resolved
// reference to that name into the `Term.cubical` it stands for. The
// signatures carry name resolution and type the UNDER-APPLIED case;
// the checker's cubical probe handles every saturated one. `I` is
// NEVER an inductive: one case split on a dimension destroys
// univalence.
//
// Each is `pub` (univalence.md Stage 6 reconnaissance, 2026-10-26):
// every existing reference to one of these sixteen names is either
// inside `init` itself or a hand-built synthetic `Scope` in a `lang`
// test/pin file, which bypasses privacy enforcement entirely -- so the
// missing `pub` was latent, not load-bearing, until a real cross-mote
// consumer (a scratch `proofs/src` probe building `Path`/`fiber`/
// `isEquiv`/`Equiv` on top of `Cubical.PathP`) tried to reach it and
// was refused with "is declared in `prelude` and is not marked `pub`".
// Confirmed by direct probe before fixing, not assumed. That consumer
// itself did not land this session -- see univalence.md's Stage 6
// reconnaissance for the two separate parser bugs that blocked it.
with Cubical {
    #[cubical "interval"] pub def I : Type
    #[cubical "i0"] pub def i0 : Cubical.I
    #[cubical "i1"] pub def i1 : Cubical.I
    #[cubical "ineg"] pub def ineg (i : Cubical.I) : Cubical.I
    #[cubical "imeet"] pub def imeet (i : Cubical.I) (j : Cubical.I) : Cubical.I
    #[cubical "ijoin"] pub def ijoin (i : Cubical.I) (j : Cubical.I) : Cubical.I
    #[cubical "pathp"] pub def PathP {u : Universe} (A : Cubical.I -> Sort u) (a : A Cubical.i0) (b : A Cubical.i1) : Sort u
    #[cubical "transp"] pub def transp (A : Cubical.I -> Type) (a : A Cubical.i0) : A Cubical.i1
    #[cubical "face_eq0"] pub def face_eq0 (i : Cubical.I) : Cubical.I
    #[cubical "face_eq1"] pub def face_eq1 (i : Cubical.I) : Cubical.I
    #[cubical "is_one"] pub def is_one (i : Cubical.I) : Type
    #[cubical "hcomp"] pub def hcomp (A : Type) (phi : Cubical.I) (u : Cubical.I -> Cubical.is_one phi -> A) (u0 : A) : A
    // The canonical inhabitant of `is_one i1` (Stage 6b). Its signature is
    // stated here for the bare/under-applied case like every other
    // primitive's; the checker's own `cubical_result_type` row is what types
    // it (`lang/typecheck/infer.mo`), and the pin
    // `test_it_is_one_types_as_a_proof_of_is_one_i1`
    // (`proofs/src/checker/cubical_props.mo`) asserts that row's answer.
    #[cubical "it_is_one"] pub def it_is_one : Cubical.is_one Cubical.i1
    // Stage 6b-ii's three. Their signatures are stated LOOSELY, and that
    // is deliberate: only the checker's own rules (`type_check_glue`,
    // `type_check_glue_intro`, `type_check_glue_elim`,
    // lang/src/typecheck/infer.mo) can state them exactly, because `w`'s
    // type mentions `Equiv`, which lives in `proofs` -- above this file.
    // What these three lines buy is name RESOLUTION and a type for the
    // under-applied case; a saturated application is typed by the rule.
    #[cubical "glue"] pub def Glue (A : Type) (phi : Cubical.I)
        (T : Cubical.is_one phi -> Type) (w : (u : Cubical.is_one phi) -> Type) : Type
    #[cubical "glue_intro"] pub def glue (A : Type) (phi : Cubical.I)
        (T : Cubical.is_one phi -> Type) (w : (u : Cubical.is_one phi) -> Type)
        (t : (u : Cubical.is_one phi) -> T u) (a : A) : Cubical.Glue A phi T w
    #[cubical "glue_elim"] pub def unglue (g : Type) : Type
}

// ── Inhabited instances ────────────────────────────────────────────
//
// Only INHABITED types get an instance: a type with no value (e.g.
// `Void`, or a phantom index) deliberately has none, which is what makes
// `Inhabited` a real obligation. `default` is an ordinary value; it never
// names an `#[opaque]` witness.

pub instance Inhabited I64 { def default : I64 := 0 }
pub instance Inhabited I32 { def default : I32 := 0i32 }
pub instance Inhabited I16 { def default : I16 := 0i16 }
pub instance Inhabited I8 { def default : I8 := 0i8 }

pub instance Inhabited U64 { def default : U64 := 0u64 }
pub instance Inhabited U32 { def default : U32 := 0u32 }
pub instance Inhabited U16 { def default : U16 := 0u16 }
pub instance Inhabited U8 { def default : U8 := 0u8 }

pub instance Inhabited F64 { def default : F64 := 0.0 }
pub instance Inhabited F32 { def default : F32 := 0.0f32 }

pub instance Inhabited Bool { def default : Bool := Bool.false }
pub instance Inhabited Unit { def default : Unit := Unit.unit }
pub instance Inhabited String { def default : String := "" }
pub instance Inhabited Ptr { def default : Ptr := Ptr.null }
pub instance Inhabited Nat { def default : Nat := Nat.zero }
pub instance {A : Type} Inhabited (List A) { def default : List A := List.empty }
pub instance {A : Type} Inhabited (Option A) { def default : Option A := Option.none }
