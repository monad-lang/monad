# Type Classes

Type classes provide ad-hoc polymorphism in Monad, similar to Haskell type
classes and Rust traits. They allow you to define interfaces that types can
implement.

## Basic Syntax

Define a type class with the `class` keyword:

```monad
class Container (F : Type -> Type) {
    def wrap : A -> F A
    def size (fa : F A) : I64
}
```

## Default Implementations

Class methods may provide a default body with `:=`:

```monad
class Describe A {
    def describe (a : A) : String := "<generic>"
    def shout (a : A) : String
}
```

Two limitations to be aware of today:

- An instance must still list every method it wants, including ones it is happy
  to take the default of. An **empty instance body `{ }` is a parse error**, so
  there is no way to write "use all the defaults". The prelude's `MonadState` is
  the first shipped class with real defaults, and `examples/state_monad.mo`
  duly spells out all five of its methods, `modify` and `get_map` included.
- Instance methods need full type annotations. `def describe x := "int"` does not
  parse; write `def describe (x : I64) : String := "int"`.

```monad
class Describe A {
    def describe (a : A) : String := "<generic>"
}

instance Describe I64 {
    def describe (x : I64) : String := "int"
}
```

## Classes with Constraints

Type classes can require other classes as constraints:

```monad,ignore
class [Functor F] Applicative (F : Type -> Type) {
    def pure : A -> F A
    def apply : F (A -> B) -> F A -> F B
}

class [Applicative M] Monad (M : Type -> Type) {
    def bind (a : M A) (f : A -> M B) : M B
    def pure : A -> M A
}
```

The `[Functor F]` syntax means "`F` must have a `Functor` instance".

## Multiple Parameters

Classes can have multiple type parameters:

```monad
class Convert A B {
    def convert : A -> B
}
```

## Default Type Parameters

A class parameter can have a default, which is used when the class is named
without one:

```monad,ignore
class FromListLiteral (L : Type -> Type := List) {
    def cons (a : A) (L A) : L A
    def empty : L A
}
```

## Type Class Constraints on Functions

Functions can require instances using bracket syntax:

```monad
def process [Functor F] {A B : Type} (f : A -> B) (fa : F A) : F B :=
    Functor.map f fa
```

## Infix Operators from Classes

You can bind an infix operator to any function, including a class method:

```monad,ignore
infix (>>=) := Monad.bind
infix (+) := HAdd.add
infix (*) := HMul.mul
```

## The Standard Classes

These are the classes that actually ship. Note where each one lives — only the
prelude ones are available without an import.

### In the prelude (no import needed)

| Class | Methods | Notes |
|-------|---------|-------|
| `Functor (F : Type -> Type)` | `map` | |
| `Applicative (F)` | `pure`, `apply` | requires `Functor` |
| `Monad (M)` | `bind`, `pure` | requires `Applicative` |
| `IndexedMonad (M)` | `pure`, `bind`, `map`, `and_then`, `lift` | indexed by two phantom parameters |
| `MonadState (M)` | `get`, `set`, `modify_get`, `modify`*, `get_map`* | * has a default body. The state type is an implicit forall, not a class parameter |
| `MonadLift m n` | `monad_lift` | lift a computation from `m` into `n` |
| `MonadLiftT m n` | `monad_lift_t` | transitive form; the reflexive `MonadLiftT m m` instance does not dispatch (see below) |
| `IndexedMonadState (M)` | `get`, `set`, `modify_get` | indexed counterpart of `MonadState` |
| `IndexedMonadLift m n` | `monad_lift` | indexed counterpart of `MonadLift` |
| `FromListLiteral (L := List)` | `cons`, `empty` | drives `[a, b, c]` |
| `HAdd A B C` / `Add A` | `add` | `+` binds `HAdd.add` |
| `HMul A B C` | `mul` | `*` |
| `Sub A` | `sub` | `-` |
| `Div A` | `div` | `/` |
| `Append A` | `append` | `++` |
| `BEq A` | `beq` | `==` |
| `BOrd A` | `lt`, `gt` | `<`, `>` |
| `ToString A` | `to_string` | |
| `Hashable A` | `hash` | |

`Add` and `HAdd` are wired to each other in both directions: an `HAdd A A A`
instance gives you `Add A`, and vice versa.

### Elsewhere in the standard library

| Class | Module | Methods |
|-------|--------|---------|
| `From T A` | `init` | `from` |
| `Semigroup A` | `init.foldable` | `combine` |
| `Monoid A` | `init.foldable` | `mempty` |
| `Foldable (T)` | `init.foldable` | `foldr`, `foldl` |
| `Traversable (T)` | `init.foldable` | `traverse` |
| `Ord A` | `std.base` | `compare` (three-way, returns `Ordering`) |
| `Semigroup A` | `std.base` | `combine` |
| `Monoid A` | `std.base` | `empty` |
| `Default A` | `std.base` | `default` |
| `Enum A` | `std.base` | `succ`, `pred`, `to_nat`, `from_nat` |
| `Bounded A` | `std.base` | `min_bound`, `max_bound` |
| `Show A` | `std.show` | `show` |
| `Debug A` | `std.debug` | `debug` |
| `Map (M := HashMap)` | `std.map` | `empty`, `insert`, `lookup`, `delete` |

> **Known wart.** `Semigroup` and `Monoid` are declared twice — once in
> `init/foldable.mo` and once in `std/base.mo` — with different method names
> (`mempty` vs `empty`). They are unrelated classes that happen to share a name.
> Import only one of them in a given file.

`Show` and `Debug` are deliberately different: `Debug` is a Rust-style
diagnostic representation (it quotes strings), `Show` is a display string.
`ToString`, in the prelude, is what the numeric types implement.

There is **no `Mul` class** (only `HMul`), and `DefaultValue` in the prelude is a
*type*, not a class — the class you want is `Default` in `std.base`.

## Instance Resolution Is Not Fully Checked

Instance resolution happens during evaluation, not during `check`. A program
that uses a class method with no matching instance will **type-check cleanly and
then fail at run time**:

```text
eval error: unresolved global: Monad.bind
```

This is a real gap, not a subtlety of the design — see the
[Maturity Matrix](./maturity.md). If you are relying on an instance, run the code
(or a `#[test]`), do not just check it.

There is a second, quieter version of the same problem. Resolution keys on the
**head** of the instance's type, so an instance whose head is a type *variable*
can never be matched. The prelude ships two — `instance MonadLiftT m m` and the
`instance {I : Type} [IndexedMonad M] Monad (M I I)` bridge — and both are, in
practice, declarations of intent. Write the concrete instance out instead; see
[Instances](./instances.md#instances-with-a-variable-head-never-match).

## Summary

- Type classes define interfaces for types
- Constraints `[C A]` require instances, on both classes and functions
- Instance methods need full annotations, and instance bodies cannot be empty
- A missing instance is currently a run-time error, not a check-time one

Next, we'll learn about **instances** and how to implement type classes.
