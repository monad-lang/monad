# Introduction

The Monad language is a dependently typed, purely functional systems
programming language that compiles through LLVM.

🌐 **[monad-lang.org](https://monad-lang.org)**

> [!WARNING]
> Monad is in **alpha release** and under heavy development. Many features are
> not implemented yet and are not tested properly. Expect breaking changes,
> incomplete functionality, and potential bugs.
>
> Read the [Maturity Matrix](./maturity.md) first — it says, area by area, what
> actually works today and what is still a sketch.

![The Monad Logo](images/monad-lang-background.png)

## Hello World

Here is a simple example:

```monad
use io {IO}
open IO {println}

def main (args : List String) : IO Unit := println "Hello, World!"
```

Save this as `hello.mo` and run it:

```bash
monad run hello.mo
```

`run` compiles the program and executes the result: a Monad program is always a
native binary. (`monad eval` interprets one instead, but reaches only a handful
of pure natives.) See [Compiling and Running](./compiling.md), which also covers
where the `monad` binary itself comes from.

## Key Features

- **Dependent types**: types can depend on values, including a `Prop` universe,
  propositional equality with a J eliminator, and length-indexed vectors
- **Type classes**: ad-hoc polymorphism with constraints and instance resolution
- **Termination checking**: recursive definitions must be structurally
  decreasing unless you opt out
- **Macros**: `defmacro`, `quote`, and compile-time reflection, which is how
  `#[derive]` is implemented — in Monad, not in the compiler
- **Pattern matching**: destructure data with `match`
- **Native functions**: call Rust code from Monad
- **IO monad**: managed side effects
- **Self-hosting**: the compiler in `lang/` is written in Monad and compiles
  itself

Linear and affine types are a stated goal of the language. Their syntax is
accepted everywhere it is meant to be — struct fields, parameters, lambdas — but
nothing is **enforced** yet; the multiplicity is dropped before type checking.
See [Linear Types](./linear-types.md).

## Quick Example

```monad
use io {IO}
open IO {println}

#[terminating]
def factorial (n : I64) : I64 :=
    if n == 0
    then 1
    else n * factorial (n - 1)

def main (args : List String) : IO Unit :=
    println (I64.to_string (factorial 5))
```

Two things in that example are worth noticing straight away, because they trip
up everyone writing their first Monad program:

- `factorial` needs `#[terminating]`. Recursion on `n - 1` is not *structurally*
  decreasing, so the termination checker rejects it unless you assert that the
  function is well-founded. See [Termination Checking](./termination.md).
- `println` takes a `String`, not "anything printable". Numbers go through
  `I64.to_string` (or the `ToString` class).

## Where to go next

- [Maturity Matrix](./maturity.md) — what works, what doesn't, at a glance
- [Getting Started](./getting-started.md) — the language tutorial
- [Compiling and Running](./compiling.md) — the compiler and its commands
- [Reference](./reference.md) — the syntax and standard-library reference
- [The Bootstrap Host](./bootstrap-host.md) — the Rust implementation, what it
  is for, and where the two differ
