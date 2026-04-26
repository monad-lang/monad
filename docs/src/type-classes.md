# Type Classes

Type classes provide ad-hoc polymorphism in Monad, similar to Haskell type classes and Rust traits. They allow you to define interfaces that types can implement.

## Basic Syntax

Define a type class with the `class` keyword:

```monad
class Functor (F : Type -> Type) {
    def map (f : A -> B) : (F A) -> F B
}
```

## Classes with Constraints

Type classes can require other classes as constraints:

```monad
class [Functor F] Applicative (F : Type -> Type) {
    def pure : A -> F A
    def apply : F (A -> B) -> F A -> F B
}

class [Applicative M] Monad (M : Type -> Type) {
    def bind (a : M A) (f : A -> M B) : M B
}
```

The `[Functor F]` syntax means "F must have a Functor instance".

## Multiple Parameters

Classes can have multiple type parameters:

```monad
class HAdd A B C {
    def add : A -> B -> C
}
```

## Constraints on Classes

A class can add constraints that must be satisfied:

```monad
class [HAdd A A A] Add A {
    def add : A -> A -> A
}
```

This means `Add A` requires `HAdd A A A` to exist.

## Standard Type Classes

### Functor

```monad
class Functor (F : Type -> Type) {
    def map (f : A -> B) : (F A) -> F B
}
```

### FromListLiteral

Used for list literal desugaring:

```monad
class FromListLiteral (L : Type -> Type) {
    def cons (a : A) (L A) : L A
    def empty : L A
}
```

### HAdd and Add

```monad
class HAdd A B C {
    def add : A -> B -> C
}

class [HAdd A A A] Add A {
    def add : A -> A -> A
}
```

### Applicative

```monad
class [Functor F] Applicative (F : Type -> Type) {
    def pure : A -> F A
    def apply : F (A -> B) -> F A -> F B
}
```

### Monad

```monad
class [Applicative M] Monad (M : Type -> Type) {
    def bind (a : M A) (f : A -> M B) : M B
}
```

### From

```monad
class From T A {
    def from (t : T) : A
}
```

### HMul

```monad
class HMul A B C {
    def mul : A -> B -> C
}
```

## Type Class Constraints

Functions can require type class instances using bracket syntax:

```monad
def process [Functor F] (f : A -> B) (fa : F A) : F B :=
    Functor.map f fa
```

The `[Functor F]` syntax means "an instance of `Functor` for `F` must exist".

## Infix Operators from Classes

You can create infix operators that reference class methods:

```monad
infix (>>=) := Monad.bind
infix (+) := I64.add
infix (*) := HMul.mul
```

## Summary

- Type classes define interfaces for types
- Constraints `[C A]` require instances
- Classes can depend on other classes
- Instance chaining enables polymorphic behavior

Next, we'll learn about **instances** and how to implement type classes.
