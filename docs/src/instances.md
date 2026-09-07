# Instances

Instances in Monad provide concrete implementations for type classes.

## Instance Declaration

Instances are declared with `instance`:

```monad
type Colour {
    red,
    green,
    blue
}

instance ToString Colour {
    def to_string (c : Colour) : String :=
        match c {
            red => "red",
            green => "green",
            blue => "blue"
        }
}
```

Every method the class declares must appear, with full type annotations on its
parameters and result. Instance bodies cannot be empty.

## Instances with Constraints

Instances can require other instances as constraints, and can bind their own
type parameters implicitly:

```monad
instance {A : Type} Append (List A) {
    def append (a b : List A) : List A := List.append a b
}
```

```monad
type Wrapper A {
    wrap (a : A)
}

instance [BEq A] BEq (Wrapper A) {
    def beq (x y : Wrapper A) : Bool :=
        match x {
            wrap a => match y {
                wrap b => BEq.beq a b
            }
        }
}
```

## Named Instances

Instances can carry a name, which is useful when several instances for the same
class would otherwise be hard to tell apart in diagnostics:

```monad
type Token {
    token (text : String)
}

instance Token.Equality : BEq Token {
    def beq (a b : Token) : Bool :=
        match a {
            token x => match b {
                token y => x == y
            }
        }
}
```

The name is recorded and then read by nothing: no syntax anywhere selects an
instance *by* name. The self-hosted compiler also accepts only a single bare
identifier here, where the bootstrap host takes a dotted path like the one above
— write `instance TokenEquality : BEq Token` for code that must compile with
both.

## A Full Monad Instance

`Monad` sits on top of `Applicative`, which sits on top of `Functor`, so a new
monad needs all three:

```monad
type Box A {
    box (a : A)
}

instance Functor Box {
    def map (f : A -> B) (b : Box A) : Box B :=
        match b {
            box a => Box.box (f a)
        }
}

instance Applicative Box {
    def pure (a : A) : Box A := Box.box a
    def apply (f : Box (A -> B)) (b : Box A) : Box B :=
        match f {
            box g => match b {
                box a => Box.box (g a)
            }
        }
}

instance Monad Box {
    def pure (a : A) : Box A := Box.box a
    def bind (b : Box A) (f : A -> Box B) : Box B :=
        match b {
            box a => f a
        }
}
```

Note that `Monad` declares **both** `bind` and `pure`; an instance that provides
only `bind` is incomplete.

## The IO Monad Instance

For comparison, here is the prelude's own instance, from `init/io.mo`:

```monad,ignore
type IO A {
    io A
}

def IO.pure (a : A) : IO A := IO.io a

instance Monad IO {
    def pure (a : A) : IO A := IO.pure a
    def bind (a : IO A) (f : A -> IO B) : IO B :=
        match a {
            io a => f a
        }
}
```

`IO.pure` is the wrapper call sites are meant to use; `IO.io` is the raw
constructor, kept so `bind` can match on it and intended to become an
implementation detail.

## Instance Resolution

Monad resolves instances by searching for one matching the required class and
type, then recursively resolving that instance's own constraints. Cyclic
constraint dependencies are detected with a visiting set.

Resolution happens during **evaluation**, not during `check`. If no instance
matches, the program type-checks and then fails at run time:

```text
eval error: unresolved global: Monad.bind
```

The most common way to hit this is assuming an instance exists when it does not.

### Instances with a variable head never match

Resolution keys on the **head** of the instance's type. An instance whose head is
a type *variable* rather than a concrete type therefore type-checks and is never
found. The prelude ships two:

```monad,ignore
instance MonadLiftT m m { … }                              // head is `m`
instance {I : Type} [IndexedMonad M] Monad (M I I) { … }    // head is `M`
```

Both are written as they would be in a language with full instance resolution,
and neither dispatches today. The workaround, which `examples/indexed_monads.mo`
uses, is to write the concrete instance out: for an indexed monad `Protocol`,
declare `instance Monad (Protocol I I)` with its own `pure` and `bind` rather
than relying on the bridge.
For example there is **no `Monad Result` instance** in the standard library, so
`>>=` on a `Result` compiles and then fails. See
[Error Handling](./error-handling.md).

## Which Instances Exist

The standard library ships 135 instances. The ones worth knowing about:

- Every fixed-width numeric type (`I8`–`I64`, `U8`–`U64`, `F32`, `F64`) has
  `Add`, `Sub`, `HMul`, `Div`, `BEq`, `BOrd`, and `ToString`
- `String` has `BEq`, `BOrd`, `ToString`, `Add`, `Append`, and `Hashable`
- `List A` has `Functor`, `FromListLiteral`, `Append`, and (with `BEq A`) `BEq`
- `Option A` has `BEq` (given `BEq A`) and `Foldable`
- `IO` and `Id` have `Functor`, `Applicative`, and `Monad`
- `HashMap` and `BTreeMap` implement `Map` (in `std.map`)
- `Array` (in `std.array`) implements **nothing** — `Array.map` and `Array.foldl`
  are plain functions, not `Functor`/`Foldable` methods

## Summary

- `instance` declares implementations for type classes
- Instances can have constraints, implicit type parameters, and names — though
  nothing selects an instance by its name
- Every class method must be given, fully annotated; empty bodies are rejected
- Instance resolution is a run-time step, so exercise your code, don't just check it

Next, we'll explore **structs**, a convenient way to define record types.
