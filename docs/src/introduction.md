# Introduction

The Monad language is a dependently typed programming language with compatibility with Rust.

🌐 **[monad-lang.org](https://monad-lang.org)**

> [!WARNING]
> Monad is in **alpha release** and under heavy development. Many features are not implemented yet and are not tested properly. Expect breaking changes, incomplete functionality, and potential bugs.

![The Monad Logo](images/monad-lang-background.png)

## Hello World

Here is a simple example:

```monad
use io
open IO

def main (args : List String) : IO Unit := println "Hello, World!"
```

Save this as `hello.mo` and run it with:

```bash
cargo run -- run hello.mo
```

## Key Features

- **Dependent types**: Types can depend on values
- **Type classes**: Ad-hoc polymorphism with constraints
- **Linear types**: Resource-safe programming with compile-time enforcement
- **Pattern matching**: Destructure data with `match`
- **Native functions**: Call Rust code from Monad
- **IO monad**: Safe side effects

## Quick Example

```monad
use io
use init
open IO

def factorial (n : I64) : I64 :=
    if n == 0
    then 1
    else n * factorial (n - 1)

def main (args : List String) : IO Unit :=
    println (factorial 5)
```
