# Error Handling

Monad provides functional error handling through the `Result` and `Option`
types, both in the prelude.

## The Result Type

`Result E A` represents a computation that may fail with an error of type `E`:

```monad,ignore
type Result E A {
    ok (a : A),
    err (e : E)
}
```

The prelude does `open Result {err, ok}`, so both constructors are available
bare.

### Basic Usage

```monad
def divide (a : I64) (b : I64) : Result String I64 :=
    if b == 0
    then err "division by zero"
    else ok (a / b)
```

### Handling Results

Use pattern matching to handle both cases:

```monad
def handle (r : Result String I64) : String :=
    match r {
        ok n => "Success: " ++ I64.to_string n,
        err e => "Error: " ++ e
    }
```

`++` is `Append.append`, which is defined for `String` — but it does not coerce.
An `I64` has to go through `I64.to_string` (or `ToString.to_string`) first.

### Chaining Results

There is **no `Monad Result` instance** in the standard library, so `>>=` does
not work on a `Result`. Writing it type-checks and then fails at run time with
`eval error: unresolved global: Monad.bind`. Chain with `match` instead:

```monad
def divide (a : I64) (b : I64) : Result String I64 :=
    if b == 0
    then err "division by zero"
    else ok (a / b)

def double_quotient (x : I64) (y : I64) : Result String I64 :=
    match divide x y {
        ok n => ok (n * 2),
        err e => err e
    }
```

If you want the monadic style, define the instances yourself for your own error
type — see [Instances](./instances.md#a-full-monad-instance) for the shape.

## The Option Type

`Option A` represents a computation that may return nothing:

```monad,ignore
type Option A {
    some (a : A),
    none
}
```

### Basic Usage

`List.first` is the prelude's canonical example:

```monad
def first_or_zero (xs : List I64) : I64 :=
    match List.first xs {
        some a => a,
        none => 0
    }
```

### Using get_or_default

```monad
def first_or (xs : List I64) : I64 :=
    Option.get_or_default 0 (List.first xs)
```

`Option` does have a `Foldable` instance (in `init.foldable`) and, given
`BEq A`, a `BEq` instance.

## Custom Error Types

Define domain-specific error types as ordinary inductive types:

```monad
type DatabaseError {
    not_found,
    connection_failed,
    permission_denied,
    timeout
}

def find_user (id : I64) : Result DatabaseError String :=
    err DatabaseError.not_found

def describe (e : DatabaseError) : String :=
    match e {
        not_found => "not found",
        connection_failed => "connection failed",
        permission_denied => "permission denied",
        timeout => "timed out"
    }
```

Note the asymmetry: in a *pattern*, constructors are bare (`not_found`), but to
*build* one you need `DatabaseError.not_found` unless you `open DatabaseError`.

## Combining with the IO Monad

```monad
use io {}
open IO {println}

def print_result (r : Result String I64) : IO Unit :=
    match r {
        ok n => println ("Success: " ++ I64.to_string n),
        err e => println ("Error: " ++ e)
    }

def main (args : List String) : IO Unit :=
    match List.first args {
        some arg => println ("First arg: " ++ arg),
        none => println "No arguments provided"
    }
```

## Errors That Are Not Values

Not every failure is a `Result`. Two other kinds exist:

- **Check-time errors** — type mismatches, unbound variables, failed termination
  checks. These come out of `monad check` with a source span. (Termination is
  the exception — only the [bootstrap host](./bootstrap-host.md) checks it.)
- **Run-time evaluation errors** — an unresolved instance, a partial match with
  no arm taken. These abort the program with an `eval error:` message. There is
  no exception mechanism and no way to catch them from Monad code.

## Summary

- `Result E A` for errors with payloads, `Option A` for simple absence
- Pattern matching handles both; `++` needs explicit `to_string` conversions
- There is no `Monad Result` instance — chain with `match`
- Define custom error types as ordinary inductive types
- Evaluation errors are not catchable values

Next, we'll look at **termination checking**.
