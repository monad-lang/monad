# Dependent Types

Monad supports dependent types, where types can depend on values. This enables
precise specifications and expressive type signatures.

## Pi Types (Function Types)

The standard function type `A -> B` is a Pi type where the result type does not
depend on the input value:

```monad
def add (a : I64) (b : I64) : I64 := a + b
```

A parameter can be named in the type, which is what makes the *dependent* case
possible — a later parameter's type may mention an earlier parameter.

## Forall Types (Implicit Arguments)

The `{A : Type}` syntax introduces implicit arguments, inferred by the checker:

```monad
def identity {A : Type} (x : A) : A := x

// Called without specifying A:
def n : I64 := identity 42
def s : String := identity "hello"
```

## Holes

The `_` placeholder is a hole: it asks the checker to infer that type.

```monad
def f (x : I64) : I64 := (x : _)
```

Holes work in **type** position inside a definition — an annotation, a parameter
type — where unification treats them as matching anything. They do **not** let
you omit a `def`'s own signature: `def x := _` is a parse error, because the
signature itself is mandatory.

> **A hole in *value* position is accepted and then goes nowhere.** Writing `_`
> where a value belongs parses, but lowering rejects it as a type-level term
> under `monad eval` and emits a void placeholder under `monad compile`. Use
> holes for types you want inferred, not as a stand-in for code you have not
> written.

## Universes

Monad's universes are written with `Sort`:

```monad
def a : Sort 1 := I64
def b : Sort 2 := Sort 1
```

`Type` and `Prop` are names for the first two levels:

| Spelling | Means |
|----------|-------|
| `Prop` (also `Pred`) | `Sort 0` — the universe of propositions |
| `Type` | `Sort 1` — the universe of ordinary types |
| `Sort 2`, `Sort 3`, … | higher universes |

So `I64 : Type`, and `Type` itself is `Sort 2`. Note that `Type` takes no
argument: **`Type 1` is not universe syntax** — it parses as `Type` applied to
the integer `1`, which is not what you want. Use `Sort 2`.

```monad
def i : Type := I64
def same : Sort 1 := I64
```

## Prop and Propositions

`Prop` is `Sort 0`, the universe of propositions. The prelude defines the
trivially true proposition:

```monad
def t : True := trivial
```

## Propositional Equality

The prelude defines equality as an inductive family in `Prop`, with the usual
single constructor `refl`:

```monad,ignore
type Eq (A : Sort 1) (a : A) (b : A) : Prop {
    refl : Eq A a a
}

/// The J eliminator
#[native "eq_rec"]
def Eq.rec (A : Sort 1) (a : A) (P : (b : A) -> Eq A a b -> Sort 1)
    (h : P a (Eq.refl a)) (b : A) (e : Eq A a b) : P b e
```

Because `refl` only builds `Eq A a a`, a value of type `Eq A x y` is a proof
that `x` and `y` are definitionally equal:

```monad
def one_is_one : Eq I64 1 1 := Eq.refl 1
def a_is_a : Eq String "a" "a" := Eq.refl "a"
```

> [!WARNING]
> **`Eq` is type-checking-only today.** Constructing and annotating an equality
> proof works, but there is no way to *use* one: `Eq.rec`'s native (`eq_rec`) is
> declared and not implemented, and pattern matching on `refl` fails at run time
> with `expected 0 constructor fields, got 1`. The prelude's own tests for `Eq`
> acknowledge this — they check that construction type-checks and stop there.
>
> So `Eq` currently documents an intent in the type system rather than enabling
> proof-carrying code.

## Length-Indexed Vectors

The prelude's `Vec` is indexed by its length, so the type records how many
elements the value has:

```monad,ignore
type Vec (len : Nat) A {
    nil : Vec Nat.zero A,
    cons (head : A) (tail : Vec len A) : Vec (Nat.succ len) A
}
```

Each constructor produces a different index, so a `Vec` of the wrong length is a
type error:

```monad
def empty_vec : Vec Nat.zero I64 := Vec.nil
def one_vec : Vec (Nat.succ Nat.zero) I64 := Vec.cons 1 Vec.nil
```

## What Is Not Implemented Yet

Monad is deliberately not a proof assistant, and the dependently typed surface
is correspondingly small. Today there is:

- **No dependent pattern matching.** A `match` does not refine the types of
  other variables in scope based on which constructor matched, so writing
  functions that consume a `Vec` while tracking its length is painful.
- **No usable equality elimination.** See the warning above: `Eq` proofs can be
  built but not consumed.
- **No tactics, no proof automation, no `Decidable`.** Proofs are written by
  hand as terms.
- **No universe polymorphism.** Levels are concrete numbers.
- **No definitional unfolding controls** (`@[reducible]` and friends).

See the [Maturity Matrix](./maturity.md) for where this sits relative to the
rest of the language.

## Summary

- Pi types are function types; naming a parameter lets later types depend on it
- `{A : Type}` introduces implicit arguments, inferred at the call site
- Holes `_` infer a type inside a definition, but never the definition's own signature
- Universes are `Sort N`; `Prop` is `Sort 0` and `Type` is `Sort 1`
- `Eq`/`refl` and `Eq.rec` give propositional equality with a J eliminator
- `Vec` is a working length-indexed vector

Next, we'll explore **macros and derive**.
