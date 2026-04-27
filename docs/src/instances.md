# Instances

Instances in Monad provide concrete implementations for type classes.

## Instance Declaration

Instances are declared with `instance`:

```monad
instance FromListLiteral List {
    def cons (a : A) (l : List A) : List A := List.cons a l
    def empty : List A := List.empty
}
```

## Instances with Constraints

Instances can require other instances as constraints:

```monad
instance [Add A] Add (List A) {
    def add (a b : List A) : List A :=
        List.append a b
}
```

## Named Instances

Instances can have optional names for organization:

```monad
instance List.FromListLiteral : FromListLiteral List {
    def cons (a : A) (l : List A) : List A := List.cons a l
    def empty : List A := List.empty
}
```

## IO Monad Instance

The IO type has a Monad instance:

```monad
instance Monad IO {
    def pure (a : A) : IO A := a
    def bind (a : IO A) (f : A -> IO B) : IO B :=
        match a {
            io a => f a
        }
}
```

## Implicit Instance Parameters

Type class parameters can be implicit and auto-resolved:

```monad
def doubleList [Add A] (xs : List A) : List A :=
    // Uses Add.add through instance resolution
    ...
```

## Instance Resolution

Monad uses instance resolution to find matching instances:

1. The type checker searches for instances matching the required class and type
2. Constraints on instances are recursively resolved
3. If no matching instance is found, a type error occurs

## Using Instances

Once an instance is defined, its methods are available through the class:

```monad
use init
use math

def result : I64 := 3 + 4  // Uses I64.add via Add instance
```

## Summary

- `instance` declares implementations for type classes
- Instances can have constraints on other instances
- Instance resolution finds matching implementations automatically
- Methods become available through class access

Next, we'll explore **structs**, a convenient way to define record types.
